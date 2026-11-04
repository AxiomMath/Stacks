module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.RingTheory.Localization.Glueing.Functions
public import StacksFrontier.Algebra.Module.IPowerTorsion.Resolution

/-!
# Flat base change of `I`-power torsion modules

Let `R → S` be a flat ring map and let `I` be an ideal of `R`. This file studies how `I`-power
torsion `R`-modules behave under base change to `S`, and resolves such a module by direct sums
of quotients `R ⧸ I ^ n`.

Throughout, "`M` is `I`-power torsion" means `IsIPowerTorsion R M I`, the predicate of
`StacksFrontier.Algebra.Module.IPowerTorsion`: every element of `M` is annihilated by some strictly
positive power of `I`.

## Main definitions

* `IPowerTorsion.unitMap`: the canonical map `M → M ⊗[R] S`, `m ↦ m ⊗ₜ 1`, whose bijectivity is
  the statement that base change does not change `M`.

## Main results

* `IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective`: for `S` flat over `R`, the
  canonical map `M → M ⊗[R] S` is bijective for every `I`-power torsion `M` if and only if
  `R ⧸ I → S ⧸ IS` is bijective.
* `IPowerTorsion.baseChange_equiv_of_quotientMap_bijective`: flat base change which is an
  isomorphism modulo a finitely generated `I` identifies `I`-primary components, is fully
  faithful once either module is `I`-power torsion, and induces an equivalence between the
  categories of `I`-power torsion modules.
* `exists_directSum_quotient_resolution` (StacksFrontier.Algebra.Module.IPowerTorsion.Resolution):
  an `I`-power torsion module admits an
  exact resolution whose terms are direct sums of modules `R ⧸ I ^ n` with `n > 0`.

## Implementation notes

Base change is written `M ⊗[R] S` when the module is the left factor (so that the unit of the
adjunction is `m ↦ m ⊗ₜ 1`) and `S ⊗[R] M` when the `S`-module structure matters, the two being
exchanged by `TensorProduct.comm`. Extension of scalars on `ModuleCat` uses `S ⊗[R] M`.

This module supplies, locally and **untagged**, the content of the Stacks Project tags 05E6,
05E8, 05E9, 05EB and 05EC. Those tags belong to another work stream, which is landing its own
conceptual providers for them; nothing here carries a `stacks` attribute and each tag's home is
left free. When the two streams meet, this module should be collapsed onto those providers and
deleted.
-/

@[expose] public section

open CategoryTheory
open scoped ChangeOfRings

namespace IPowerTorsion

universe u v w v₁ v₂ v₃

/-! ### Base change along a flat map that is an isomorphism modulo `I` -/

/-- The unit of the base-change adjunction: the `R`-linear map `M → M ⊗[R] S`, `m ↦ m ⊗ₜ 1`. -/
abbrev unitMap (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M] :
    M →ₗ[R] TensorProduct R M S :=
  (TensorProduct.mk R M S).flip 1

/-- The diagram chase used in the induction on the exponent: if the unit is bijective on a
submodule and on the corresponding quotient, then it is bijective on the whole module. -/
private lemma bijective_unitMap_of_extension
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M] (N : Submodule R M)
    (hflat : Module.Flat R S)
    (hN : Function.Bijective (unitMap R S N))
    (hQ : Function.Bijective (unitMap R S (M ⧸ N))) :
    Function.Bijective (unitMap R S M) := by
  let i : N →ₗ[R] M := N.subtype
  let p : M →ₗ[R] M ⧸ N := N.mkQ
  have hi : Function.Injective (LinearMap.rTensor S i) := by
    let _ := hflat
    exact Module.Flat.rTensor_preserves_injective_linearMap i N.injective_subtype
  have hp : Function.Surjective (LinearMap.rTensor S p) :=
    LinearMap.rTensor_surjective S N.mkQ_surjective
  constructor
  · intro x y hxy
    have hp : p (x - y) = 0 := by
      apply hQ.1
      rw [map_sub, map_sub, map_zero]
      apply sub_eq_zero.mpr
      simpa [unitMap, p] using congrArg (LinearMap.rTensor S p) hxy
    obtain ⟨n, hn⟩ : ∃ n : N, (n : M) = x - y :=
      ⟨⟨x - y, (Submodule.Quotient.mk_eq_zero N).mp hp⟩, rfl⟩
    have hun : unitMap R S N n = 0 := by
      apply hi
      calc
        LinearMap.rTensor S i (unitMap R S N n) = unitMap R S M (i n) := by
          simp [unitMap, i]
        _ = unitMap R S M (x - y) := by simpa [i] using congrArg (unitMap R S M) hn
        _ = 0 := by rwa [map_sub, sub_eq_zero]
    have : n = 0 := hN.1 (hun.trans (map_zero _).symm)
    apply sub_eq_zero.mp
    rw [← hn, this]
    rfl
  · intro z
    obtain ⟨q, hq⟩ := hQ.2 ((LinearMap.rTensor S p) z)
    obtain ⟨m, hm⟩ := N.mkQ_surjective q
    have hzker : z - unitMap R S M m ∈ LinearMap.ker (LinearMap.rTensor S p) := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      simpa [unitMap, p, hm] using hq.symm
    rw [LinearMap.exact_iff.1
      (Module.Flat.rTensor_exact S (LinearMap.exact_subtype_mkQ N))] at hzker
    obtain ⟨n, hn⟩ := hzker
    obtain ⟨n', hn'⟩ := hN.2 n
    refine ⟨m + i n', ?_⟩
    rw [map_add]
    calc
      unitMap R S M m + unitMap R S M (i n') =
          unitMap R S M m + LinearMap.rTensor S i (unitMap R S N n') := by
            simp [unitMap, i]
      _ = unitMap R S M m + LinearMap.rTensor S i n := by rw [hn']
      _ = z := by
        rw [hn]
        abel

/-- If `R ⧸ I → S ⧸ IS` is surjective, then the unit is surjective on every module annihilated
by `I`. -/
private lemma unitMap_surjective_of_annihilator
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hq : Function.Surjective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M] (hM : I ≤ Module.annihilator R M) :
    Function.Surjective (unitMap R S M) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, by simp⟩
  | tmul m s =>
      obtain ⟨r, hr⟩ := hq (Ideal.Quotient.mk _ s)
      induction r using Quotient.inductionOn' with
      | _ r =>
        refine ⟨r • m, ?_⟩
        show (r • m) ⊗ₜ[R] (1 : S) = m ⊗ₜ[R] s
        rw [TensorProduct.smul_tmul]
        have hd : s - algebraMap R S r ∈ I.map (algebraMap R S) := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          show Ideal.Quotient.mk _ s -
            (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
              Ideal.le_comap_map) (Ideal.Quotient.mk I r) = 0
          exact sub_eq_zero.mpr hr.symm
        have hz : m ⊗ₜ[R] (s - algebraMap R S r) = 0 := by
          change s - algebraMap R S r ∈
            Submodule.span S (algebraMap R S '' (↑I : Set R)) at hd
          have hall : ∀ u : S, m ⊗ₜ[R] (u * (s - algebraMap R S r)) = 0 := by
            refine Submodule.span_induction
              (p := fun t _ ↦ ∀ u : S, m ⊗ₜ[R] (u * t) = 0) ?_ ?_ ?_ ?_ hd
            · rintro _ ⟨a, ha, rfl⟩ u
              rw [mul_comm u, ← Algebra.smul_def, TensorProduct.tmul_smul]
              calc
                (a • m) ⊗ₜ[R] u = (0 : M) ⊗ₜ[R] u := congrArg (fun z : M ↦ z ⊗ₜ[R] u)
                  ((Module.mem_annihilator.mp (hM ha)) m)
                _ = 0 := by simp
            · simp
            · intro x y _ _ hx hy u
              simp [mul_add, TensorProduct.tmul_add, hx, hy]
            · intro a x _ hx u
              simpa [mul_assoc] using hx (u * a)
          simpa using hall 1
        have hs : m ⊗ₜ[R] s = m ⊗ₜ[R] algebraMap R S r :=
          sub_eq_zero.mp (by simpa [TensorProduct.tmul_sub] using hz)
        simpa [Algebra.smul_def] using hs.symm

/-- If `R ⧸ I → S ⧸ IS` is bijective and `S` is flat, then the unit is bijective on every module
annihilated by `I`. -/
private lemma bijective_unitMap_of_annihilator
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (hflat : Module.Flat R S)
    (I : Ideal R) (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M] (hM : I ≤ Module.annihilator R M) :
    Function.Bijective (unitMap R S M) := by
  let _ := hflat
  let q : R ⧸ I →+* S ⧸ I.map (algebraMap R S) :=
    Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map
  let e : TensorProduct R (R ⧸ I) S ≃ₗ[R] S ⧸ I.map (algebraMap R S) :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv.restrictScalars R
  have he (x : R ⧸ I) : e (unitMap R S (R ⧸ I) x) = q x := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      show (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm
        (Ideal.Quotient.mk I x ⊗ₜ[R] (1 : S)) =
          Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
            Ideal.le_comap_map (Ideal.Quotient.mk I x)
      rw [AlgEquiv.symm_apply_eq]
      simpa using
        ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).commutes
          (Ideal.Quotient.mk I x)).symm
  have hA : Function.Bijective (unitMap R S (R ⧸ I)) := by
    constructor
    · intro x y hxy
      apply hq.1
      rw [← he, ← he]
      exact congrArg e hxy
    · intro z
      obtain ⟨x, hx⟩ := hq.2 (e z)
      refine ⟨x, e.injective ?_⟩
      calc
        e (unitMap R S (R ⧸ I) x) = q x := he x
        _ = e z := hx
  have hsurj : Function.Surjective (unitMap R S M) :=
    unitMap_surjective_of_annihilator R S I hq.2 M hM
  refine ⟨?_, hsurj⟩
  intro x y hxy
  let d := x - y
  let N : Submodule R M := R ∙ d
  let g : R →ₗ[R] N := (LinearMap.toSpanSingleton R M d).codRestrict N (by
    intro r
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d))
  have hIg : I ≤ LinearMap.ker g := by
    intro a ha
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show a • d = 0
    dsimp [d]
    rw [smul_sub, (Module.mem_annihilator.mp (hM ha)) x,
      (Module.mem_annihilator.mp (hM ha)) y, sub_zero]
  let f : R ⧸ I →ₗ[R] N := I.liftQ g hIg
  have hf_surj : Function.Surjective f := by
    intro n
    have hn : (n : M) ∈ LinearMap.range (LinearMap.toSpanSingleton R M d) := by
      rw [LinearMap.range_toSpanSingleton]
      exact n.property
    obtain ⟨r, hr⟩ := hn
    refine ⟨Ideal.Quotient.mk I r, ?_⟩
    show g r = n
    ext
    show r • d = (n : M)
    exact hr
  have hd0 : unitMap R S N ⟨d, Submodule.mem_span_singleton_self d⟩ = 0 := by
    apply (Module.Flat.rTensor_preserves_injective_linearMap N.subtype N.injective_subtype)
    rw [show LinearMap.rTensor S N.subtype
      (unitMap R S N ⟨d, Submodule.mem_span_singleton_self d⟩) = unitMap R S M d by
        simp [unitMap, N]]
    simp only [map_zero]
    dsimp [d]
    rw [TensorProduct.sub_tmul, sub_eq_zero]
    exact hxy
  have hf1 : f 1 = ⟨d, Submodule.mem_span_singleton_self d⟩ := by
    show g 1 = _
    ext
    show (1 : R) • d = d
    simp
  have hone : LinearMap.rTensor S f (unitMap R S (R ⧸ I) 1) = 0 := by
    calc
      LinearMap.rTensor S f (unitMap R S (R ⧸ I) 1) = unitMap R S N (f 1) := by
        simp [unitMap]
      _ = unitMap R S N ⟨d, Submodule.mem_span_singleton_self d⟩ := by
        rw [hf1]
      _ = 0 := hd0
  have hexact := Module.Flat.rTensor_exact S f.exact_subtype_ker_map
  rw [LinearMap.exact_iff] at hexact
  have honeker : unitMap R S (R ⧸ I) 1 ∈ LinearMap.ker (LinearMap.rTensor S f) := by
    simpa [LinearMap.mem_ker] using hone
  rw [hexact] at honeker
  obtain ⟨z, hz⟩ := honeker
  have hkerann : I ≤ Module.annihilator R (LinearMap.ker f) := by
    intro a ha
    rw [Module.mem_annihilator]
    intro k
    apply Subtype.ext
    show (Ideal.Quotient.mk I a) * (k : R ⧸ I) = 0
    rw [show Ideal.Quotient.mk I a = 0 by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
  obtain ⟨k, hk⟩ := unitMap_surjective_of_annihilator R S I hq.2
    (LinearMap.ker f) hkerann z
  have hu : unitMap R S (R ⧸ I) ((LinearMap.ker f).subtype k) =
      unitMap R S (R ⧸ I) 1 := by
    rw [← hz, ← hk]
    simp [unitMap]
  have hk1 := hA.1 hu
  have hk0 : f ((LinearMap.ker f).subtype k) = 0 := k.property
  have hd : d = 0 := by
    have heq := congrArg f hk1
    rw [hk0, hf1] at heq
    exact congrArg Subtype.val heq.symm
  exact sub_eq_zero.mp hd

/-- Induction on the exponent: the unit is bijective on every module annihilated by `I ^ n`. -/
private lemma bijective_unitMap_of_pow_annihilator
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    ∀ (n : ℕ) (M : Type w) [AddCommGroup M] [Module R M],
      I ^ n ≤ Module.annihilator R M → Function.Bijective (unitMap R S M) := by
  intro n
  induction n with
  | zero =>
      intro M _ _ hM
      have : (1 : R) ∈ Module.annihilator R M := hM (by simp)
      have hzero (x : M) : x = 0 := by simpa using (Module.mem_annihilator.mp this) x
      have : Subsingleton M := ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩
      exact ⟨fun x y _ ↦ Subsingleton.elim x y, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  | succ n ih =>
      intro M _ _ hM
      let N : Submodule R M := I ^ n • ⊤
      apply bijective_unitMap_of_extension R S N hflat
      · apply bijective_unitMap_of_annihilator R S hflat I hq
        intro a ha
        rw [Module.mem_annihilator]
        rintro ⟨x, hx⟩
        apply Subtype.ext
        simp only [Submodule.coe_zero, Submodule.coe_smul_of_tower]
        refine Submodule.smul_induction_on (p := fun z : M ↦ a • z = 0) hx ?_ ?_
        · intro b hb y _
          simpa [smul_smul, mul_comm] using
            (Module.mem_annihilator.mp (hM (by
            rw [pow_succ]
            simpa [mul_comm] using
              Submodule.mul_mem_mul (M := I ^ n) (N := I) (m := b) (n := a) hb ha))) y
        · intro x y hx hy
          simp only [smul_add, hx, hy, add_zero]
      · apply ih (M ⧸ N)
        intro a ha
        rw [Module.mem_annihilator]
        intro x
        obtain ⟨x, rfl⟩ := N.mkQ_surjective x
        show Submodule.Quotient.mk (a • x) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul ha Submodule.mem_top

/-- Suppose that `S` is flat over `R`. The canonical map from every `I`-power torsion `R`-module
to its base change to `S` is an isomorphism if and only if the canonical map
`R ⧸ I → S ⧸ IS` is an isomorphism. -/
theorem baseChange_bijective_iff_quotientMap_bijective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R)
    (hflat : Module.Flat R S) :
    ((∀ (M : Type (max u v w)) [AddCommGroup M] [Module R M],
        IsIPowerTorsion R M I →
          Function.Bijective ((TensorProduct.mk R M S).flip 1)) ↔
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) := by
  let q : R ⧸ I →+* S ⧸ I.map (algebraMap R S) :=
    Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map
  let e : TensorProduct R (R ⧸ I) S ≃ₗ[R] S ⧸ I.map (algebraMap R S) :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv.restrictScalars R
  have he (x : R ⧸ I) : e (unitMap R S (R ⧸ I) x) = q x := by
    induction x using Quotient.inductionOn' with
    | _ x =>
      show (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm
        (Ideal.Quotient.mk I x ⊗ₜ[R] (1 : S)) = q (Ideal.Quotient.mk I x)
      rw [AlgEquiv.symm_apply_eq]
      simpa [q] using
        ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).commutes
          (Ideal.Quotient.mk I x)).symm
  constructor
  · intro h
    let A := ULift.{max u v w} (R ⧸ I)
    let l : A ≃ₗ[R] R ⧸ I :=
      { toFun := ULift.down
        invFun := ULift.up
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have ht : IsIPowerTorsion R A I := by
      intro x
      refine ⟨1, by simp, ?_⟩
      intro a ha
      rcases x with ⟨x⟩
      apply ULift.ext
      induction x using Quotient.inductionOn' with
      | _ x =>
        show Ideal.Quotient.mk I (a * x) = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (I.mul_mem_right x (by simpa using ha))
    have hu := h A ht
    let lt : TensorProduct R A S ≃ₗ[R] TensorProduct R (R ⧸ I) S := l.rTensor S
    constructor
    · intro x y hxy
      apply l.symm.injective
      apply hu.1
      apply lt.injective
      rw [show lt (unitMap R S A (l.symm x)) = unitMap R S (R ⧸ I) x by
        simp [lt, l, unitMap],
        show lt (unitMap R S A (l.symm y)) = unitMap R S (R ⧸ I) y by
        simp [lt, l, unitMap]]
      apply e.injective
      rw [he, he]
      exact hxy
    · intro z
      obtain ⟨x, hx⟩ := hu.2 (lt.symm (e.symm z))
      refine ⟨l x, ?_⟩
      rw [← he]
      calc
        e (unitMap R S (R ⧸ I) (l x)) = e (lt (unitMap R S A x)) := by
          congr 1
        _ = z := by rw [hx]; simp
  · intro hq M _ _ hM
    let _ := hflat
    have cyclic_ann (m : M) : ∃ n : ℕ, I ^ n ≤ Module.annihilator R (R ∙ m) := by
      obtain ⟨n, _, hn⟩ := hM m
      refine ⟨n, ?_⟩
      intro a ha
      rw [Module.mem_annihilator]
      intro x
      have hx : (x : M) ∈ LinearMap.range (LinearMap.toSpanSingleton R M m) := by
        rw [LinearMap.range_toSpanSingleton]
        exact x.property
      obtain ⟨r, hr⟩ := hx
      apply Subtype.ext
      show a • (x : M) = 0
      rw [← hr]
      show a • (r • m) = 0
      rw [smul_smul, mul_comm a r, ← smul_smul, hn a ha, smul_zero]
    constructor
    · intro x y hxy
      let d := x - y
      let N : Submodule R M := R ∙ d
      obtain ⟨n, hn⟩ := cyclic_ann d
      have hN := bijective_unitMap_of_pow_annihilator R S I hflat hq n N hn
      apply sub_eq_zero.mp
      show d = 0
      have hz : unitMap R S N ⟨d, Submodule.mem_span_singleton_self d⟩ = 0 := by
        apply (Module.Flat.rTensor_preserves_injective_linearMap N.subtype N.injective_subtype)
        rw [show LinearMap.rTensor S N.subtype
          (unitMap R S N ⟨d, Submodule.mem_span_singleton_self d⟩) = unitMap R S M d by
            simp [unitMap, N]]
        simp only [map_zero]
        dsimp [d]
        rw [TensorProduct.sub_tmul, sub_eq_zero]
        exact hxy
      have := hN.1 (hz.trans (map_zero _).symm)
      exact congrArg Subtype.val this
    · intro z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, by simp⟩
      | add x y hx hy =>
          obtain ⟨x, rfl⟩ := hx
          obtain ⟨y, rfl⟩ := hy
          exact ⟨x + y, by simp⟩
      | tmul m s =>
          let N : Submodule R M := R ∙ m
          obtain ⟨n, hn⟩ := cyclic_ann m
          have hN := bijective_unitMap_of_pow_annihilator R S I hflat hq n N hn
          obtain ⟨x, hx⟩ := hN.2 (⟨m, Submodule.mem_span_singleton_self m⟩ ⊗ₜ[R] s)
          refine ⟨(x : M), ?_⟩
          calc
            unitMap R S M (x : M) = LinearMap.rTensor S N.subtype (unitMap R S N x) := by
              simp [unitMap, N]
            _ = LinearMap.rTensor S N.subtype
                (⟨m, Submodule.mem_span_singleton_self m⟩ ⊗ₜ[R] s) := by rw [hx]
            _ = m ⊗ₜ[R] s := by simp [N]

/-! ### Primary components, quotients and extensions -/

/-- For a finitely generated `I`, an element whose multiples by `I` all lie in the `I`-primary
component lies in the `I`-primary component itself. -/
private theorem mem_primaryComponent_of_smul_mem
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    {M : Type*} [AddCommGroup M] [Module R M] (x : M)
    (hx : ∀ a ∈ I, a • x ∈ Ideal.primaryComponent M I) :
    x ∈ Ideal.primaryComponent M I := by
  have hrad : I ≤ (Ideal.torsionOf R M x).radical := by
    intro a ha
    obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M I (a • x)).mp (hx a ha)
    refine (Ideal.mem_radical_iff.mpr ⟨n + 1, ?_⟩)
    rw [Ideal.mem_torsionOf_iff, pow_succ, mul_smul]
    exact (Submodule.mem_torsionBySet_iff _ _).mp hn
      ⟨a ^ n, Ideal.pow_mem_pow ha n⟩
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad hI
  exact (Ideal.primaryComponent_mem M I x).mpr ⟨n,
    (Submodule.mem_torsionBySet_iff _ _).mpr fun ⟨a, ha⟩ ↦
      (Ideal.mem_torsionOf_iff x a).mp (hn ha)⟩

/-- For a finitely generated `I`, no nonzero element of `M ⧸ M[I^∞]` is annihilated by `I`. -/
private theorem torsionBySet_quotient_primaryComponent_eq_bot
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule.torsionBySet R (M ⧸ (Ideal.primaryComponent M I)) (I : Set R) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := (Ideal.primaryComponent M I).mkQ_surjective q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply mem_primaryComponent_of_smul_mem I hI x
  intro a ha
  apply (Submodule.Quotient.mk_eq_zero _).mp
  show a • (Ideal.primaryComponent M I).mkQ x = 0
  exact (Submodule.mem_torsionBySet_iff _ _).mp hq ⟨a, ha⟩

/-- If no nonzero element of `M` is annihilated by `I`, the same holds for every positive power
of `I`. -/
private theorem torsionBySet_pow_eq_bot
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M]
    (h : Submodule.torsionBySet R M (I : Set R) = ⊥) :
    ∀ n : ℕ, 1 ≤ n →
      Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) = ⊥ := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using h
  | succ k ih =>
      rw [Submodule.eq_bot_iff]
      intro m hm
      have hmI : m ∈ Submodule.torsionBySet R M (I : Set R) := by
        rw [Submodule.mem_torsionBySet_iff]
        rintro ⟨a, ha⟩
        have ham : a • m ∈
            Submodule.torsionBySet R M ((I ^ (1 + k) : Ideal R) : Set R) := by
          rw [Submodule.mem_torsionBySet_iff]
          rintro ⟨b, hb⟩
          rw [smul_smul]
          rw [Submodule.mem_torsionBySet_iff] at hm
          apply hm ⟨b * a, ?_⟩
          rw [show 1 + (k + 1) = (1 + k) + 1 by omega, pow_succ]
          exact Ideal.mul_mem_mul hb ha
        rwa [ih (by omega)] at ham
      rwa [h] at hmI

/-- Having no nonzero element annihilated by a finitely generated ideal is detected by
injectivity of the multiplication map `m ↦ (f i • m)ᵢ` attached to a finite generating family. -/
private lemma torsionBySet_eq_bot_iff_bigPhi_injective
    {A : Type u} [CommRing A] (J : Ideal A)
    {Q : Type w} [AddCommGroup Q] [Module A Q]
    (t : ℕ) (f : Fin t → A) (hf : J = Ideal.span (Set.range f)) :
    Submodule.torsionBySet A Q (J : Set A) = ⊥ ↔
      Function.Injective (bigPhi (M := Q) t f) := by
  rw [bigPhi_injective_iff_commonAnnihilator]
  constructor
  · intro h m hm
    have hm' : m ∈ Submodule.torsionBySet A Q (Set.range f) := by
      rw [Submodule.mem_torsionBySet_iff]
      rintro ⟨_, i, rfl⟩
      exact hm i
    rwa [Submodule.torsionBySet_eq_torsionBySet_span, ← hf, h] at hm'
  · intro h
    rw [Submodule.eq_bot_iff]
    intro m hm
    apply h m
    intro i
    rw [Submodule.mem_torsionBySet_iff] at hm
    exact hm ⟨f i, hf.symm ▸ Ideal.subset_span (Set.mem_range_self i)⟩

/-- Injectivity of the multiplication map is preserved by flat base change. -/
public lemma bigPhi_baseChange_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {Q : Type w} [AddCommGroup Q] [Module R Q] [Module.Flat R S]
    (t : ℕ) (f : Fin t → R) (h : Function.Injective (bigPhi (M := Q) t f)) :
    Function.Injective (bigPhi (M := TensorProduct R S Q) t (algebraMap R S ∘ f)) := by
  let a := (bigPhi (M := Q) t f).lTensor S
  let e := TensorProduct.piRight R S S (fun _ : Fin t ↦ Q)
  have ha : Function.Injective a :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := S) _ h
  have he : Function.Injective e := e.injective
  have heq (z : TensorProduct R S Q) :
      e (a z) = bigPhi t (algebraMap R S ∘ f) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul s q => ext i; simp [a, e, bigPhi, Algebra.smul_def]
    | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy
  intro x y hxy
  apply ha
  apply he
  simpa only [heq] using hxy

/-- Having no nonzero element annihilated by a finitely generated `I` is preserved by flat base
change. -/
public lemma torsionBySet_baseChange_eq_bot
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) {Q : Type w} [AddCommGroup Q] [Module R Q]
    [Module.Flat R S] (hQ : Submodule.torsionBySet R Q (I : Set R) = ⊥) :
    Submodule.torsionBySet S (TensorProduct R S Q)
      (I.map (algebraMap R S) : Set S) = ⊥ := by
  obtain ⟨A, hA⟩ := hI
  obtain ⟨t, f, hf⟩ := A.finite_toSet.fin_embedding
  have hgen : I = Ideal.span (Set.range f) := by
    rw [hf]
    exact hA.symm
  have hgenS : I.map (algebraMap R S) =
      Ideal.span (Set.range (algebraMap R S ∘ f)) := by
    rw [hgen, Ideal.map_span]
    congr 1
    ext s
    simp [Function.comp_def]
  apply (torsionBySet_eq_bot_iff_bigPhi_injective
    (I.map (algebraMap R S)) t (algebraMap R S ∘ f) hgenS).2
  apply bigPhi_baseChange_injective
  exact (torsionBySet_eq_bot_iff_bigPhi_injective I t f hgen).1 hQ

/-- The `I`-primary component of a module is `I`-power torsion. -/
public lemma primaryComponent_isIPowerTorsion
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type w} [AddCommGroup M] [Module R M] :
    IsIPowerTorsion R (Ideal.primaryComponent M I) I := by
  rintro ⟨m, hm⟩
  rw [Ideal.primaryComponent_mem] at hm
  obtain ⟨n, hn⟩ := hm
  rw [Submodule.mem_torsionBySet_iff] at hn
  exact ⟨n + 1, n.succ_pos, fun a ha ↦ Subtype.ext (hn ⟨a, Ideal.pow_le_pow_right n.le_succ ha⟩)⟩

/-- The unit sends the `I`-primary component into the `IS`-primary component of the base
change. -/
public lemma one_tmul_mem_primaryComponent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) {M : Type w} [AddCommGroup M] [Module R M]
    (x : Ideal.primaryComponent M I) :
    (1 : S) ⊗ₜ[R] x.1 ∈
      Ideal.primaryComponent (TensorProduct R S M) (I.map (algebraMap R S)) := by
  have hx := x.property
  rw [Ideal.primaryComponent_mem] at hx ⊢
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, ?_⟩
  rw [Submodule.mem_torsionBySet_iff] at hn ⊢
  rintro ⟨b, hb⟩
  rw [← Ideal.map_pow] at hb
  let J : Ideal S := {
    carrier := {c | c • ((1 : S) ⊗ₜ[R] x.1) = 0}
    zero_mem' := by simp
    add_mem' := by
      intro a b ha hb
      show (a + b) • ((1 : S) ⊗ₜ[R] x.1) = 0
      rw [add_smul, ha, hb, add_zero]
    smul_mem' := by intro a b hb; simpa [smul_smul, mul_comm] using congrArg (a • ·) hb }
  have hle : (I ^ n).map (algebraMap R S) ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show algebraMap R S a • ((1 : S) ⊗ₜ[R] x.1) = 0
    show (algebraMap R S a * 1) ⊗ₜ[R] x.1 = 0
    rw [mul_one, show algebraMap R S a = a • (1 : S) by simp [Algebra.smul_def],
      TensorProduct.smul_tmul,
      hn ⟨a, ha⟩, TensorProduct.tmul_zero]
  exact hle hb

/-- An `S`-module which is `IS`-power torsion is `I`-power torsion for the restricted
`R`-structure. -/
public lemma isIPowerTorsion_restrictScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) {M : Type w} [AddCommGroup M] [Module S M]
    (hM : IsIPowerTorsion S M (I.map (algebraMap R S))) :
    letI : Module R M := Module.compHom M (algebraMap R S)
    IsIPowerTorsion R M I := by
  let : Module R M := Module.compHom M (algebraMap R S)
  intro m
  obtain ⟨n, hn, hnm⟩ := hM m
  refine ⟨n, hn, fun a ha ↦ ?_⟩
  show algebraMap R S a • m = 0
  apply hnm
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

/-- Flat base change which is an isomorphism modulo a finitely generated `I` identifies the
`I`-primary component of `M` with the `IS`-primary component of `S ⊗[R] M`. -/
public lemma primaryComponent_baseChange_equiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : Type (max u v w)) [AddCommGroup M] [Module R M] :
    ∃ e : Ideal.primaryComponent M I ≃ₗ[R]
        Ideal.primaryComponent (TensorProduct R S M) (I.map (algebraMap R S)),
      ∀ x, (e x : TensorProduct R S M) = (1 : S) ⊗ₜ[R] x.1 := by
  let P := Ideal.primaryComponent M I
  let η : M →ₗ[R] TensorProduct R S M := TensorProduct.mk R S M 1
  let e0 : P →ₗ[R] Ideal.primaryComponent (TensorProduct R S M)
      (I.map (algebraMap R S)) := {
    toFun x := ⟨η x.1, one_tmul_mem_primaryComponent I x⟩
    map_add' x y := by ext; exact map_add η x.1 y.1
    map_smul' r x := by ext; simp [η] }
  have hunit :=
    (baseChange_bijective_iff_quotientMap_bijective R S I hflat).2 hq
  have he0inj : Function.Injective e0 := by
    intro x y hxy
    apply (hunit P (primaryComponent_isIPowerTorsion I)).1
    apply Module.Flat.rTensor_preserves_injective_linearMap P.subtype Subtype.val_injective
    have h := congrArg (TensorProduct.comm R S M) (congrArg Subtype.val hxy)
    simpa [e0, η] using h
  have hQ0 := torsionBySet_quotient_primaryComponent_eq_bot I hI M
  let q : M →ₗ[R] M ⧸ (Ideal.primaryComponent M I) :=
    (Ideal.primaryComponent M I).mkQ
  let tq : TensorProduct R S M →ₗ[S]
      TensorProduct R S (M ⧸ (Ideal.primaryComponent M I)) :=
    LinearMap.baseChange S q
  have hQtors : Submodule.torsionBySet S
      (TensorProduct R S (M ⧸ (Ideal.primaryComponent M I)))
      (I.map (algebraMap R S) : Set S) = ⊥ := by
    let : Module.Flat R S := hflat
    exact torsionBySet_baseChange_eq_bot I hI hQ0
  have he0surj : Function.Surjective e0 := by
    intro y
    have hty : tq y.1 ∈ Ideal.primaryComponent
        (TensorProduct R S (M ⧸ (Ideal.primaryComponent M I)))
        (I.map (algebraMap R S)) :=
      Ideal.primaryComponent_map_mem _ tq y
    rw [Ideal.primaryComponent_mem] at hty
    obtain ⟨n, hn⟩ := hty
    have hz : tq y.1 = 0 := by
      have hpow : Submodule.torsionBySet S
          (TensorProduct R S (M ⧸ (Ideal.primaryComponent M I)))
          (((I.map (algebraMap R S)) ^ n : Ideal S) : Set S) = ⊥ := by
        rcases n with _ | n
        · simp
        · exact torsionBySet_pow_eq_bot (I.map (algebraMap R S))
            hQtors (n + 1) (by omega)
      rw [hpow] at hn
      exact hn
    have hex := Module.Flat.lTensor_exact S (LinearMap.exact_subtype_mkQ P)
    have hyrange : y.1 ∈ LinearMap.range (P.subtype.lTensor S) := by
      rw [← hex.linearMap_ker_eq]
      show (q.lTensor S) y.1 = 0
      exact hz
    obtain ⟨z, hz⟩ := hyrange
    obtain ⟨x, hx⟩ := (hunit P (primaryComponent_isIPowerTorsion I)).2
      ((TensorProduct.comm R S P) z)
    refine ⟨x, Subtype.ext ?_⟩
    show η x.1 = y.1
    rw [← hz]
    apply (TensorProduct.comm R S M).injective
    rw [← LinearMap.rTensor_comm, ← hx]
    rfl
  exact ⟨LinearEquiv.ofBijective e0 ⟨he0inj, he0surj⟩, fun x ↦ rfl⟩

/-- Every element of an `I`-power torsion module lies in the `I`-primary component. -/
public lemma mem_primaryComponent_of_isIPowerTorsion
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type w} [AddCommGroup M] [Module R M]
    (hM : IsIPowerTorsion R M I) (m : M) :
    m ∈ Ideal.primaryComponent M I := by
  obtain ⟨n, _, hn⟩ := hM m
  exact (Ideal.primaryComponent_mem M I m).mpr
    ⟨n, (Submodule.mem_torsionBySet_iff _ _).mpr fun a ↦ hn a.1 a.2⟩

/-- A module all of whose elements lie in the `I`-primary component is `I`-power torsion. -/
public lemma isIPowerTorsion_of_mem_primaryComponent
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type w} [AddCommGroup M] [Module R M]
    (hM : ∀ m : M, m ∈ Ideal.primaryComponent M I) :
    IsIPowerTorsion R M I := by
  intro m
  have hm := hM m
  rw [Ideal.primaryComponent_mem] at hm
  obtain ⟨n, hn⟩ := hm
  rw [Submodule.mem_torsionBySet_iff] at hn
  exact ⟨n + 1, n.succ_pos, fun a ha ↦ hn ⟨a, Ideal.pow_le_pow_right n.le_succ ha⟩⟩

/-- Bijectivity of `m ↦ m ⊗ₜ 1` transfers to bijectivity of `m ↦ 1 ⊗ₜ m`. -/
public lemma one_tmul_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {M : Type w} [AddCommGroup M] [Module R M]
    (h : Function.Bijective ((TensorProduct.mk R M S).flip 1)) :
    Function.Bijective (TensorProduct.mk R S M 1) := by
  constructor
  · intro x y hxy
    apply h.1
    simpa using congrArg (TensorProduct.comm R S M) hxy
  · intro z
    obtain ⟨m, hm⟩ := h.2 ((TensorProduct.comm R S M) z)
    refine ⟨m, ?_⟩
    apply (TensorProduct.comm R S M).injective
    simpa using hm

/-- The base change of an `I`-power torsion module is `IS`-power torsion, as soon as the unit is
bijective on it. -/
public lemma extension_isIPowerTorsion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) {M : Type w} [AddCommGroup M] [Module R M]
    (hM : IsIPowerTorsion R M I)
    (hunit : Function.Bijective ((TensorProduct.mk R M S).flip 1)) :
    IsIPowerTorsion S (TensorProduct R S M)
      (I.map (algebraMap R S)) := by
  apply isIPowerTorsion_of_mem_primaryComponent
  intro z
  obtain ⟨m, hm⟩ := (one_tmul_bijective hunit).2 z
  rw [← hm]
  exact one_tmul_mem_primaryComponent I
    ⟨m, mem_primaryComponent_of_isIPowerTorsion I hM m⟩

/-- Base change is bijective on `Hom`-modules as soon as one of the two modules is `I`-power
torsion. -/
public lemma hom_baseChange_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M N : Type (max u v w)) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (hMN : IsIPowerTorsion R M I ∨ IsIPowerTorsion R N I) :
    Function.Bijective (fun f : M →ₗ[R] N ↦ LinearMap.baseChange S f) := by
  obtain ⟨eN, heN⟩ := primaryComponent_baseChange_equiv I hI hflat hq N
  have hunit :=
    (baseChange_bijective_iff_quotientMap_bijective R S I hflat).2 hq
  let ηM : M →ₗ[R] TensorProduct R S M := TensorProduct.mk R S M 1
  have himage (g : TensorProduct R S M →ₗ[S] TensorProduct R S N) (m : M) :
      g ((1 : S) ⊗ₜ[R] m) ∈
        Ideal.primaryComponent (TensorProduct R S N) (I.map (algebraMap R S)) := by
    rcases hMN with hM | hN
    · exact Ideal.primaryComponent_map_mem _ g
        ⟨(1 : S) ⊗ₜ[R] m, one_tmul_mem_primaryComponent I
          ⟨m, mem_primaryComponent_of_isIPowerTorsion I hM m⟩⟩
    · obtain ⟨n, hn⟩ := (hunit N hN).2
          ((TensorProduct.comm R S N) (g ((1 : S) ⊗ₜ[R] m)))
      have hn' : (1 : S) ⊗ₜ[R] n = g ((1 : S) ⊗ₜ[R] m) := by
        apply (TensorProduct.comm R S N).injective
        simpa using hn
      rw [← hn']
      simpa using one_tmul_mem_primaryComponent I
        ⟨n, mem_primaryComponent_of_isIPowerTorsion I hN n⟩
  constructor
  · intro f g hfg
    ext m
    have h' : (1 : S) ⊗ₜ[R] f m = (1 : S) ⊗ₜ[R] g m :=
      DFunLike.congr_fun hfg ((1 : S) ⊗ₜ[R] m)
    have hmem (φ : M →ₗ[R] N) : φ m ∈ Ideal.primaryComponent N I := hMN.elim
      (fun hM ↦ Ideal.primaryComponent_map_mem I φ
        ⟨m, mem_primaryComponent_of_isIPowerTorsion I hM m⟩)
      (fun hN ↦ mem_primaryComponent_of_isIPowerTorsion I hN (φ m))
    have : (⟨f m, hmem f⟩ : Ideal.primaryComponent N I) = ⟨g m, hmem g⟩ :=
      eN.injective (Subtype.ext (by simpa [heN] using h'))
    exact congrArg Subtype.val this
  · intro g
    let gr : TensorProduct R S M →ₗ[R] TensorProduct R S N := g.restrictScalars R
    let z : M →ₗ[R] Ideal.primaryComponent (TensorProduct R S N)
        (I.map (algebraMap R S)) := {
      toFun m := ⟨gr (ηM m), himage g m⟩
      map_add' m m' := by ext; exact (gr.comp ηM).map_add m m'
      map_smul' r m := by ext; exact (gr.comp ηM).map_smul r m }
    let f : M →ₗ[R] N :=
      (Ideal.primaryComponent N I).subtype.comp (eN.symm.toLinearMap.comp z)
    refine ⟨f, ?_⟩
    ext m
    show (1 : S) ⊗ₜ[R] f m = g ((1 : S) ⊗ₜ[R] m)
    show (1 : S) ⊗ₜ[R] (eN.symm (z m)).1 = (z m).1
    rw [← heN, LinearEquiv.apply_symm_apply]

/-- The counit of the extension/restriction adjunction is bijective on every `IS`-power torsion
`S`-module. -/
theorem extendRestrictScalarsAdj_counit_app_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat.{max u v w} S)
    (hM : IsIPowerTorsion S M (I.map (algebraMap R S))) :
    Function.Bijective
      ((ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} (algebraMap R S)).counit.app M) := by
  let N := (ModuleCat.restrictScalars (algebraMap R S)).obj M
  have hr : IsIPowerTorsion R N I := isIPowerTorsion_restrictScalars I hM
  have hunit :=
    (baseChange_bijective_iff_quotientMap_bijective R S I hflat).2 hq N hr
  have hu : Function.Bijective (TensorProduct.mk R S N 1) :=
    one_tmul_bijective hunit
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let eS : S ≃ₗ[R] S' := {
    toFun := id
    invFun := id
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := by
      intro r s
      show r • s = algebraMap R S r * s
      exact Algebra.smul_def r s }
  let eT : TensorProduct R S N ≃ₗ[R] TensorProduct R S' N :=
    TensorProduct.congr eS (LinearEquiv.refl R N)
  have hcat : Function.Bijective (fun m : N => (eS (1 : S)) ⊗ₜ[R] m) :=
    eT.bijective.comp hu
  let c := (ModuleCat.extendRestrictScalarsAdj.{max u w, u, v} (algebraMap R S)).counit.app M
  have hc (m : M) : c ((1 : S) ⊗ₜ[R] m) = m :=
    ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul.{u, v, max u w}
      (algebraMap R S) M m
  constructor
  · intro x y hxy
    obtain ⟨m, rfl⟩ := hcat.2 x
    obtain ⟨n, rfl⟩ := hcat.2 y
    have : m = n := by
      change c ((1 : S) ⊗ₜ[R] m) = c ((1 : S) ⊗ₜ[R] n) at hxy
      exact (hc m).symm.trans (hxy.trans (hc n))
    rw [this]
  · intro m
    exact ⟨(1 : S) ⊗ₜ[R] m, hc m⟩

/-- Extension of scalars on `ModuleCat` is the tensor product `S ⊗[R] M`. -/
public noncomputable def tensorModuleCatEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{max u v w} R) :
    TensorProduct R S M ≃ₗ[S]
      (ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).obj M := by
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let eS : S ≃ₗ[S] S' := {
    toFun := id
    invFun := id
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  let : IsScalarTower R S S' := ⟨by
    intro r s x
    rw [Algebra.smul_def]
    have hs : r • (s • x) = algebraMap R S r • (s • x) :=
      ModuleCat.restrictScalars.smul_def (algebraMap R S) r (s • x)
    rw [hs, mul_smul]⟩
  exact TensorProduct.AlgebraTensorModule.congr eS (LinearEquiv.refl R M)

/-- `tensorModuleCatEquiv` sends a pure tensor `s ⊗ₜ m` to the pure tensor `s ⊗ₜ m` of the
extension of scalars. -/
public lemma tensorModuleCatEquiv_tmul
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{max u v w} R) (s : S) (m : M) :
    tensorModuleCatEquiv (S := S) M (s ⊗ₜ[R] m) =
      s ⊗ₜ[R, algebraMap R S] m := by
  rfl

/-- Morphisms between extensions of scalars are `S`-linear maps between the tensor products. -/
public noncomputable def tensorModuleCatHomEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M N : ModuleCat.{max u v w} R) :
    ((ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).obj M ⟶
      (ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).obj N) ≃
      (TensorProduct R S M →ₗ[S] TensorProduct R S N) := by
  let eM := tensorModuleCatEquiv (S := S) M
  let eN := tensorModuleCatEquiv (S := S) N
  exact {
    toFun g := eN.symm.toLinearMap.comp (g.hom.comp eM.toLinearMap)
    invFun f := ModuleCat.ofHom
      (X := (ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).obj M)
      (Y := (ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).obj N)
      (eN.toLinearMap.comp (f.comp eM.symm.toLinearMap))
    left_inv g := by
      apply ModuleCat.homEquiv.injective
      apply LinearMap.ext
      intro x
      change eN (eN.symm (g (eM (eM.symm x)))) = g x
      simp
    right_inv f := by
      apply LinearMap.ext
      intro x
      change eN.symm (eN (f (eM.symm (eM x)))) = f x
      simp }

/-- Under `tensorModuleCatHomEquiv`, the extension of scalars of an `R`-linear map `f` is its
base change `LinearMap.baseChange S f`. -/
public lemma tensorModuleCatHomEquiv_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M N : ModuleCat.{max u v w} R) (f : M →ₗ[R] N) :
    tensorModuleCatHomEquiv (S := S) M N
      ((ModuleCat.extendScalars (algebraMap R S)).map (ModuleCat.ofHom f)) =
      LinearMap.baseChange S f := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s m
  show (tensorModuleCatEquiv N).symm
    ((ModuleCat.extendScalars (algebraMap R S)).map (ModuleCat.ofHom f)
      (tensorModuleCatEquiv M (s ⊗ₜ[R] m))) = s ⊗ₜ[R] f m
  rw [tensorModuleCatEquiv_tmul]
  show (tensorModuleCatEquiv N).symm
    (s ⊗ₜ[R, algebraMap R S] f m) = s ⊗ₜ[R] f m
  rw [← tensorModuleCatEquiv_tmul]
  exact (tensorModuleCatEquiv N).symm_apply_apply _

/-- The `ModuleCat` form of `hom_baseChange_bijective`. -/
public lemma moduleCatHom_baseChange_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M N : ModuleCat.{max u v w} R)
    (hMN : IsIPowerTorsion R M I ∨ IsIPowerTorsion R N I) :
    Function.Bijective (fun f : M →ₗ[R] N =>
      (ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).map
        (ModuleCat.ofHom f)) := by
  let E := tensorModuleCatHomEquiv.{u, v, w} (S := S) M N
  have h := hom_baseChange_bijective I hI hflat hq M N hMN
  constructor
  · intro f g hfg
    apply h.1
    show LinearMap.baseChange S f = LinearMap.baseChange S g
    calc
      _ = E ((ModuleCat.extendScalars (algebraMap R S)).map (ModuleCat.ofHom f)) :=
        (tensorModuleCatHomEquiv_map.{u, v, w} M N f).symm
      _ = E ((ModuleCat.extendScalars (algebraMap R S)).map (ModuleCat.ofHom g)) :=
        congrArg E hfg
      _ = LinearMap.baseChange S g :=
        tensorModuleCatHomEquiv_map.{u, v, w} M N g
  · intro g
    obtain ⟨f, hf⟩ := h.2 (E g)
    refine ⟨f, E.injective ?_⟩
    rw [tensorModuleCatHomEquiv_map.{u, v, w} M N f]
    exact hf

/-- Flat base change which is an isomorphism modulo a finitely generated ideal identifies
`I`-power torsion submodules, induces an isomorphism on Hom sets whenever either module is
`I`-power torsion, and defines an equivalence between the corresponding full subcategories of
modules. -/
theorem baseChange_equiv_of_quotientMap_bijective
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    (∀ (M : Type (max u v w)) [AddCommGroup M] [Module R M],
      ∃ e : Ideal.primaryComponent M I ≃ₗ[R]
          (Ideal.primaryComponent (TensorProduct R S M) (I.map (algebraMap R S))),
        ∀ x, (e x : TensorProduct R S M) = (1 : S) ⊗ₜ[R] x.1) ∧
    (∀ (M N : Type (max u v w)) [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N],
      (IsIPowerTorsion R M I ∨ IsIPowerTorsion R N I) →
        Function.Bijective (fun f : M →ₗ[R] N =>
          (ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).map
            (ModuleCat.ofHom f))) ∧
    (∃ e :
        (ObjectProperty.FullSubcategory (fun M : ModuleCat.{max u v w} R =>
          IsIPowerTorsion R M I)) ≌
        (ObjectProperty.FullSubcategory (fun M : ModuleCat.{max u v w} S =>
          IsIPowerTorsion S M (I.map (algebraMap R S)))),
      Nonempty (e.functor ⋙ ObjectProperty.ι _ ≅
        ObjectProperty.ι _ ⋙
          ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro M _ _
    exact primaryComponent_baseChange_equiv I hI hflat hq M
  · intro M N _ _ _ _ hMN
    exact moduleCatHom_baseChange_bijective I hI hflat hq
      (ModuleCat.of R M) (ModuleCat.of R N) hMN
  · let P : ObjectProperty (ModuleCat.{max u v w} R) :=
      fun M => IsIPowerTorsion R M I
    let Q : ObjectProperty (ModuleCat.{max u v w} S) :=
      fun M => IsIPowerTorsion S M (I.map (algebraMap R S))
    let B := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)
    have hunit :=
      (baseChange_bijective_iff_quotientMap_bijective R S I hflat).2 hq
    have hF : ∀ X : P.FullSubcategory, Q ((P.ι ⋙ B).obj X) := by
      intro X
      let e := tensorModuleCatEquiv (S := S) X.obj
      have ht := extension_isIPowerTorsion I X.2 (hunit X.obj X.2)
      intro z
      obtain ⟨n, hn, han⟩ := ht (e.symm z)
      refine ⟨n, hn, ?_⟩
      intro a ha
      have hzero := han a ha
      have heq := congrArg e hzero
      simpa only [map_smul, map_zero, LinearEquiv.apply_symm_apply] using heq
    let F := Q.lift (P.ι ⋙ B) hF
    have hfaithful : F.Faithful := by
      constructor
      intro X Y f g hfg
      apply ObjectProperty.hom_ext
      apply ModuleCat.homEquiv.injective
      apply (moduleCatHom_baseChange_bijective I hI hflat hq
        X.obj Y.obj (Or.inl X.2)).1
      exact congrArg (fun z : F.obj X ⟶ F.obj Y => z.hom) hfg
    have hfull : F.Full := by
      constructor
      intro X Y g
      obtain ⟨f, hf⟩ :=
        (moduleCatHom_baseChange_bijective I hI hflat hq
          X.obj Y.obj (Or.inl X.2)).2 g.hom
      refine ⟨ObjectProperty.homMk (ModuleCat.ofHom f), ?_⟩
      apply ObjectProperty.hom_ext
      exact hf
    have hess : F.EssSurj := by
      constructor
      intro Y
      let N := (ModuleCat.restrictScalars (algebraMap R S)).obj Y.obj
      have hN : P N := isIPowerTorsion_restrictScalars I Y.2
      let X : P.FullSubcategory := ⟨N, hN⟩
      let c := (ModuleCat.extendRestrictScalarsAdj.{max u w, u, v}
        (algebraMap R S)).counit.app Y.obj
      have : IsIso c := (ConcreteCategory.isIso_iff_bijective c).2
        (extendRestrictScalarsAdj_counit_app_bijective I hflat hq Y.obj Y.2)
      exact ⟨X, ⟨ObjectProperty.isoMk Q (asIso c)⟩⟩
    let : F.IsEquivalence := ⟨hfaithful, hfull, hess⟩
    exact ⟨F.asEquivalence, ⟨Q.liftCompιIso (P.ι ⋙ B) hF⟩⟩

/-! ### Resolutions by direct sums of `R ⧸ I ^ n` -/

open scoped DirectSum


end IPowerTorsion
