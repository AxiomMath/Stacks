module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.OrzechProperty
public import StacksFrontier.Algebra.MittagLeffler.Defs
public import StacksFrontier.Algebra.MittagLeffler.Henselian
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# Associated primes of tensor products of direct sums of finite modules

Let `R` be a local ring and `S` an `R`-algebra. If an `S`-module `N` is, as an `R`-module, a
direct sum of finite modules, then every associated prime of `N ⊗[R] M` meets the closed fibre
over `R`, for an arbitrary `R`-module `M`.

The proof reduces to a finite subsum `P` of the direct-sum decomposition carrying a witness of
the associated prime. Writing `1 = f + g` with `f` annihilating the witness and `g` in the
extended maximal ideal, the `P`-component of multiplication by `f` is surjective modulo
`𝔪 P`, hence surjective by Nakayama and bijective by the Orzech property; tensoring with `M`
then kills the witness, a contradiction.

Over a henselian local ring the direct-sum hypothesis is automatic for a countably generated
Mittag-Leffler module, which gives the second result.

## Main results

* `Stacks.PureModules.associatedPrime_add_map_maximalIdeal_ne_top_of_directSum_finite`: an
  associated prime of the tensor product of a direct sum of finite modules is not comaximal
  with the extension of the maximal ideal of `R`.
* `Stacks.PureModules.associatedPrime_add_map_maximalIdeal_ne_top_of_countable_mittagLeffler`:
  the same conclusion for a countably generated Mittag-Leffler module over a henselian local
  ring.

## Implementation notes

The direct-sum decomposition is given by an `R`-linear equivalence, the extension of the
maximal ideal is its image under `algebraMap R S`, and associatedness is
`IsAssociatedPrimeStacks`. Countable generation is expressed by a countable spanning set; the
universe of the module contains a copy of the universe of `R`, as in the direct-sum theorem for
Mittag-Leffler modules over henselian local rings.

## References

* [Stacks Project, Tag 05IU](https://stacks.math.columbia.edu/tag/05IU)
* [Stacks Project, Tag 05IV](https://stacks.math.columbia.edu/tag/05IV)
-/

@[expose] public section

namespace Stacks.PureModules

open scoped DirectSum TensorProduct Pointwise

universe u v w x y z

/-- The inclusion of the direct sum over a finite subset of the index type into the whole
direct sum. -/
private noncomputable def finiteDirectSumIncl {R ι : Type*} [CommRing R]
    {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [DecidableEq ι]
    (s : Finset ι) : (⨁ i : {i // i ∈ s}, F i.1) →ₗ[R] ⨁ i : ι, F i := by
  classical
  exact DirectSum.toModule R {i // i ∈ s} (⨁ i : ι, F i) fun i => DirectSum.lof R ι F i.1

private lemma finiteDirectSumIncl_lof {R ι : Type*} [CommRing R]
    {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [DecidableEq ι] (s : Finset ι) (j : {i // i ∈ s}) (x : F j.1) :
    finiteDirectSumIncl (R := R) (F := F) s
      (DirectSum.lof R {i // i ∈ s} (fun i => F i.1) j x) = DirectSum.lof R ι F j.1 x := by
  change DirectSum.toModule R {i // i ∈ s} (⨁ i : ι, F i)
    (fun i => DirectSum.lof R ι F i.1)
    (DirectSum.lof R {i // i ∈ s} (fun i => F i.1) j x) = _
  exact DirectSum.toModule_lof (R := R) (M := fun i : {i // i ∈ s} => F i.1)
    (N := ⨁ i : ι, F i) (φ := fun i => DirectSum.lof R ι F i.1) j x

private lemma finiteDirectSumIncl_subtypeDomain {R ι : Type*} [CommRing R]
    {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    [DecidableEq ι] (s : Finset ι) (v : ⨁ i : ι, F i) :
    finiteDirectSumIncl (R := R) (F := F) s (v.subtypeDomain (fun i => i ∈ s)) =
      v.filter (fun i => i ∈ s) := by
  classical
  induction v using DirectSum.induction_on with
  | zero => simp [finiteDirectSumIncl]
  | of i x =>
      rw [← DirectSum.lof_eq_of R ι F i x]
      by_cases hi : i ∈ s
      · let hj : {i // i ∈ s} := ⟨i, hi⟩
        have hsub : (DirectSum.lof R ι F i x).subtypeDomain (fun i => i ∈ s) =
            DirectSum.lof R {i // i ∈ s} (fun j => F j.1) hj x := by
          ext j
          change DirectSum.component R ι F j.1 (DirectSum.lof R ι F i x) =
            DirectSum.component R {i // i ∈ s} (fun j => F j.1) j
              (DirectSum.lof R {i // i ∈ s} (fun j => F j.1) hj x)
          rw [DirectSum.component.of, DirectSum.component.of]
          by_cases hji : (j : ι) = i
          · have hj' : j = hj := Subtype.ext hji
            subst j
            simp [hj]
          · have hji' : i ≠ (j : ι) := fun h => hji h.symm
            have hjne : hj ≠ j := by
              intro h
              subst j
              exact hji rfl
            simp [hji', hjne]
        rw [hsub, finiteDirectSumIncl_lof]
        ext j
        by_cases hj : j ∈ s
        · rw [DFinsupp.filter_apply_pos _ hj]
        · rw [DFinsupp.filter_apply_neg _ hj]
          change DirectSum.component R ι F j (DirectSum.lof R ι F i x) = 0
          rw [DirectSum.component.of]
          simp [show i ≠ j from fun h => hj (h ▸ hi)]
      · have hsub : (DirectSum.lof R ι F i x).subtypeDomain (fun i => i ∈ s) = 0 := by
          ext j
          change DirectSum.component R ι F j.1 (DirectSum.lof R ι F i x) = 0
          rw [DirectSum.component.of]
          simp [show i ≠ (j : ι) from fun h => hi (h ▸ j.2)]
        rw [hsub]
        ext j
        by_cases hj : j ∈ s
        · rw [DFinsupp.filter_apply_pos _ hj]
          change 0 = DirectSum.component R ι F j (DirectSum.lof R ι F i x)
          rw [DirectSum.component.of]
          simp [show i ≠ j from fun h => hi (h ▸ hj)]
        · simp [DFinsupp.filter_apply_neg _ hj, finiteDirectSumIncl]
  | add x y hx hy => rw [DFinsupp.subtypeDomain_add, DFinsupp.filter_add, map_add, hx, hy]

/-- The projection of the direct sum onto the direct sum over a finite subset of the index
type. -/
private noncomputable def finiteDirectSumProj {R ι : Type*} [CommRing R]
    {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [DecidableEq ι]
    (s : Finset ι) : (⨁ i : ι, F i) →ₗ[R] ⨁ i : {i // i ∈ s}, F i.1 := by
  classical
  exact DFinsupp.subtypeDomainLinearMap R F (fun i => i ∈ s)

private lemma finiteDirectSumProj_comp_incl {R ι : Type*} [CommRing R]
    {F : ι → Type*} [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] [DecidableEq ι]
    (s : Finset ι) :
    (finiteDirectSumProj (R := R) (F := F) s).comp (finiteDirectSumIncl s) = LinearMap.id := by
  classical
  refine LinearMap.ext fun x => ?_
  induction x using DirectSum.induction_on with
  | zero => simp
  | of i y =>
      change finiteDirectSumProj (R := R) (F := F) s
        (finiteDirectSumIncl (R := R) (F := F) s
          (DirectSum.lof R {i // i ∈ s} (fun j => F j.1) i y)) = _
      rw [finiteDirectSumIncl_lof, ← DirectSum.lof_eq_of R {i // i ∈ s} (fun j => F j.1) i y]
      change DFinsupp.subtypeDomain (fun k => k ∈ s)
        (DirectSum.lof R ι F i.1 y) = DirectSum.lof R {i // i ∈ s} (fun j => F j.1) i y
      ext j
      change (DFinsupp.subtypeDomain (fun k => k ∈ s) (DirectSum.lof R ι F i.1 y)) j =
        (DirectSum.lof R {i // i ∈ s} (fun j => F j.1) i y) j
      rw [DFinsupp.subtypeDomain_apply]
      change DirectSum.component R ι F j.1 (DirectSum.lof R ι F i.1 y) =
        DirectSum.component R {i // i ∈ s} (fun j => F j.1) j
          (DirectSum.lof R {i // i ∈ s} (fun j => F j.1) i y)
      rw [DirectSum.component.of, DirectSum.component.of]
      by_cases hji : i = j
      · subst j
        simp
      · have hji' : i.1 ≠ j.1 := fun h => hji (Subtype.ext h)
        simp [hji, hji']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private lemma directSumLeft_comp_map_finiteDirectSumIncl {R ι : Type*} (M : Type*)
    [CommRing R] [AddCommGroup M] [Module R M] [DecidableEq ι]
    (F : ι → Type*) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)] (s : Finset ι) :
    (TensorProduct.directSumLeft R R F M).toLinearMap.comp
        (TensorProduct.map (finiteDirectSumIncl s) LinearMap.id) =
      (finiteDirectSumIncl (R := R) (F := fun i => F i ⊗[R] M) s).comp
        (TensorProduct.directSumLeft R R (fun i : {i // i ∈ s} => F i.1) M).toLinearMap := by
  refine LinearMap.ext fun t => ?_
  induction t using TensorProduct.inductionOn with
  | tmul x m =>
      induction x using DirectSum.induction_on with
      | zero => simp
      | of j y =>
          rw [← DirectSum.lof_eq_of R {i // i ∈ s} (fun j => F j.1) j y]
          change TensorProduct.directSumLeft R R F M
              (finiteDirectSumIncl (R := R) (F := F) s
                (DirectSum.lof R {i // i ∈ s} (fun j => F j.1) j y) ⊗ₜ[R] m) =
            finiteDirectSumIncl (R := R) (F := fun i => F i ⊗[R] M) s
              (TensorProduct.directSumLeft R R (fun i : {i // i ∈ s} => F i.1) M
                (DirectSum.lof R {i // i ∈ s} (fun j => F j.1) j y ⊗ₜ[R] m))
          rw [finiteDirectSumIncl_lof, TensorProduct.directSumLeft_tmul_lof,
            TensorProduct.directSumLeft_tmul_lof, finiteDirectSumIncl_lof]
      | add x y hx hy => rw [TensorProduct.add_tmul, map_add, map_add, hx, hy]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

private lemma tensorMap_comp_left {R A B C M : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] [AddCommGroup M] [Module R M]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    TensorProduct.map (g.comp f) (LinearMap.id : M →ₗ[R] M) =
      (TensorProduct.map g (LinearMap.id : M →ₗ[R] M)).comp
        (TensorProduct.map f (LinearMap.id : M →ₗ[R] M)) := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Every element of `N ⊗[R] M`, for `N` a direct sum of the family `F`, comes from the
tensor product of a finite subsum of `F` with `M`. -/
private lemma tensor_lift_finite_support {R ι M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [DecidableEq ι]
    (F : ι → Type*) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    (N : Type*) [AddCommGroup N] [Module R N]
    (e : N ≃ₗ[R] ⨁ i, F i) (z : N ⊗[R] M) :
    ∃ (s : Finset ι) (w : (⨁ i : {i // i ∈ s}, F i.1) ⊗[R] M),
      TensorProduct.map ((e.symm.toLinearMap).comp (finiteDirectSumIncl s))
        LinearMap.id w = z := by
  classical
  let v := TensorProduct.directSumLeft R R F M (TensorProduct.map e.toLinearMap LinearMap.id z)
  let s := v.support
  let J := {i // i ∈ s}
  let w₀ : ⨁ i : J, F i.1 ⊗[R] M := v.subtypeDomain (fun i => i ∈ s)
  let k : (⨁ i : J, F i.1 ⊗[R] M) →ₗ[R] ⨁ i : ι, F i ⊗[R] M :=
    finiteDirectSumIncl (R := R) (F := fun i => F i ⊗[R] M) s
  have hk : k w₀ = v := by
    change finiteDirectSumIncl (R := R) (F := fun i => F i ⊗[R] M) s
      (v.subtypeDomain (fun i => i ∈ s)) = v
    rw [finiteDirectSumIncl_subtypeDomain]
    ext i
    by_cases hi : v i = 0
    · simp [hi]
    · simp [s, hi]
  let w := (TensorProduct.directSumLeft R R (fun i : J => F i.1) M).symm w₀
  let a : (⨁ i : J, F i.1) →ₗ[R] ⨁ i, F i := finiteDirectSumIncl s
  refine ⟨s, w, ?_⟩
  have hmap : TensorProduct.map a LinearMap.id w =
      TensorProduct.map e.toLinearMap LinearMap.id z :=
    (TensorProduct.directSumLeft R R F M).injective <|
      (LinearMap.congr_fun (directSumLeft_comp_map_finiteDirectSumIncl M F s) w).trans
        ((congrArg k (LinearEquiv.apply_symm_apply _ w₀)).trans hk)
  rw [tensorMap_comp_left, LinearMap.comp_apply, hmap, ← LinearMap.comp_apply,
    ← tensorMap_comp_left]
  simp

/-- Multiplication by an element of `S` on an `S`-module, viewed as an endomorphism of the
underlying `R`-module. -/
private def scalarEnd {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (s : S) : N →ₗ[R] N where
  toFun := fun x => s • x
  map_add' := smul_add s
  map_smul' r x := smul_comm s r x

private lemma tensorMap_scalarEnd_eq_smul {R S N M : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [AddCommGroup M] [Module R M] (s : S) (z : N ⊗[R] M) :
    TensorProduct.map (scalarEnd (R := R) (S := S) (N := N) s)
      (LinearMap.id : M →ₗ[R] M) z = s • z := by
  induction z using TensorProduct.inductionOn with
  | tmul n m => rfl
  | add x y hx hy => rw [map_add, smul_add, hx, hy]

private lemma linearMap_mem_ideal_smul_top {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (f : M →ₗ[R] N) {x : M}
    (hx : x ∈ (I : Set R) • (⊤ : Submodule R M)) :
    f x ∈ (I : Set R) • (⊤ : Submodule R N) := by
  induction x, hx using Submodule.set_smul_inductionOn with
  | smul₀ hr hn =>
      rw [map_smul]
      exact Submodule.mem_set_smul_of_mem_mem hr (by simp)
  | smul₁ r hm ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ r ih
  | add _ _ hx hy => simpa [map_add] using add_mem hx hy
  | zero => simp

/-- If `g` lies in the extension of an ideal `I` of `R` to `S`, then multiplication by `g` maps
an `S`-module into `I • ⊤`. -/
private lemma smul_mem_set_smul_top_of_mem_map {R S N : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (I : Ideal R) {g : S} (hg : g ∈ I.map (algebraMap R S)) (x : N) :
    g • x ∈ (I : Set R) • (⊤ : Submodule R N) := by
  apply Submodule.span_induction (R := S) (M := S) (s := algebraMap R S '' (I : Set R))
    (p := fun c _ => c • x ∈ (I : Set R) • (⊤ : Submodule R N))
  · rintro y ⟨r, hr, rfl⟩
    rw [IsScalarTower.algebraMap_smul]
    exact Submodule.mem_set_smul_of_mem_mem hr (by simp)
  · simp
  · intro _ _ _ _ h₁ h₂
    simpa [add_smul] using add_mem h₁ h₂
  · intro c _ _ ih
    rw [smul_eq_mul, mul_smul]
    exact linearMap_mem_ideal_smul_top I (scalarEnd (R := R) c) ih
  · exact hg

/-- Over a local ring, an endomorphism `a` of a finite module with `a + b = id` for some `b`
landing in `𝔪 • ⊤` is surjective. -/
private lemma surjective_of_add_eq_id_of_mem_maximalIdeal_smul {R P : Type*} [CommRing R]
    [IsLocalRing R] [AddCommGroup P] [Module R P] [Module.Finite R P] (a b : P →ₗ[R] P)
    (hab : a + b = LinearMap.id)
    (hb : ∀ x, b x ∈ ((IsLocalRing.maximalIdeal R : Ideal R) : Set R) • (⊤ : Submodule R P)) :
    Function.Surjective a := by
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let Q : Submodule R P := m • (⊤ : Submodule R P)
  have hmodSurj : Function.Surjective (Q.mkQ.comp a) := by
    intro y
    obtain ⟨x, rfl⟩ := Q.mkQ_surjective y
    refine ⟨x, ?_⟩
    have hbzero : Q.mkQ (b x) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      change b x ∈ m • (⊤ : Submodule R P)
      exact Submodule.set_smul_le _ _ _ (fun r y hr hy => Submodule.smul_mem_smul hr hy) (hb x)
    have hsumx : a x + b x = x := LinearMap.congr_fun hab x
    rw [LinearMap.comp_apply, ← congrArg Q.mkQ hsumx, map_add, hbzero, add_zero]
  exact LinearMap.surjective_of_surjective_comp_mkQ a m (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    (by simpa [Q] using hmodSurj)

/-- **Stacks Project, Tag 05IU.** An associated prime of a tensor product of a direct sum of
finite modules cannot be comaximal with the closed fibre of a local base ring. -/
@[stacks 05IU]
theorem associatedPrime_add_map_maximalIdeal_ne_top_of_directSum_finite
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (ι : Type x) (F : ι → Type y)
    [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
    (hF : ∀ i, Module.Finite R (F i))
    (e : N ≃ₗ[R] ⨁ i, F i)
    (M : Type z) [AddCommGroup M] [Module R M]
    (q : Ideal S) (hq : IsAssociatedPrimeStacks S (N ⊗[R] M) q) :
    q + (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≠ ⊤ := by
  classical
  rcases hq with ⟨hqPrime, z, hzcol⟩
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let K : Ideal S := m.map (algebraMap R S)
  by_contra hbad
  have htop : q ⊔ K = ⊤ := by simpa [Ideal.add_eq_sup] using hbad
  obtain ⟨f, hf, g, hg, hfg⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top : (1 : S) ∈ q ⊔ K)
  have hfcol : f ∈ (⊥ : Submodule S (N ⊗[R] M)).colon (Submodule.span S {z}) := hzcol ▸ hf
  have hfz : f • z = 0 := by
    simpa [Submodule.mem_colon_span_singleton] using hfcol
  have hz_ne : z ≠ 0 := fun hz => hqPrime.ne_top (hzcol.symm.trans (by simp [hz]))
  obtain ⟨s, w, hw⟩ := tensor_lift_finite_support (R := R) (ι := ι) (M := M) F N e z
  let J := {i // i ∈ s}
  let P := ⨁ i : J, F i.1
  let incP : P →ₗ[R] ⨁ i : ι, F i := finiteDirectSumIncl s
  let projP : (⨁ i : ι, F i) →ₗ[R] P := finiteDirectSumProj s
  let incN : P →ₗ[R] N := e.symm.toLinearMap.comp incP
  let projN : N →ₗ[R] P := projP.comp e.toLinearMap
  let a : P →ₗ[R] P := (projN.comp (scalarEnd (R := R) (S := S) f)).comp incN
  let b : P →ₗ[R] P := (projN.comp (scalarEnd (R := R) (S := S) g)).comp incN
  let _ : Fintype J := Fintype.ofFinite J
  let _ : ∀ i : J, Module.Finite R (F i.1) := fun i => hF i.1
  let _ : Module.Finite R P := by infer_instance
  have hE : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id :=
    LinearMap.ext e.apply_symm_apply
  have hRetract : projN.comp incN = LinearMap.id := by
    simpa [projN, incN, LinearMap.comp_assoc, hE] using
      finiteDirectSumProj_comp_incl (R := R) (F := F) s
  have hab : a + b = LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    change projN (f • incN x) + projN (g • incN x) = x
    rw [← map_add, ← add_smul, hfg, one_smul]
    exact LinearMap.congr_fun hRetract x
  have hsurj : Function.Surjective a :=
    surjective_of_add_eq_id_of_mem_maximalIdeal_smul a b hab fun x =>
      linearMap_mem_ideal_smul_top m projN (smul_mem_set_smul_top_of_mem_map m hg (incN x))
  have habij : Function.Bijective a :=
    OrzechProperty.bijective_of_surjective_endomorphism a hsurj
  have haTensorInj : Function.Injective (TensorProduct.map a (LinearMap.id : M →ₗ[R] M)) :=
    (TensorProduct.congr (LinearEquiv.ofBijective a habij) (LinearEquiv.refl R M)).injective
  have hinc : TensorProduct.map incN (LinearMap.id : M →ₗ[R] M) w = z := by
    simpa [incN, incP] using hw
  have hkill : TensorProduct.map a (LinearMap.id : M →ₗ[R] M) w = 0 := by
    dsimp only [a]
    rw [tensorMap_comp_left, tensorMap_comp_left, LinearMap.comp_apply, LinearMap.comp_apply,
      hinc, tensorMap_scalarEnd_eq_smul, hfz, map_zero]
  have hwzero : w = 0 := haTensorInj (by simpa using hkill)
  exact hz_ne (by rw [← hinc, hwzero, map_zero])

/-- **Stacks Project, Tag 05IV.** An associated prime of a tensor product of a countably
generated Mittag-Leffler module over a henselian local ring cannot be comaximal with the
closed fibre. -/
@[stacks 05IV]
theorem associatedPrime_add_map_maximalIdeal_ne_top_of_countable_mittagLeffler
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [HenselianLocalRing R]
    [Algebra R S]
    (N : Type w) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    [Small.{w} R]
    (hcg : ∃ t : Set N, t.Countable ∧ Submodule.span R t = ⊤)
    (hML : IsMittagLeffler.{u, w, w, w, w} R N)
    (M : Type x) [AddCommGroup M] [Module R M]
    (q : Ideal S) (hq : IsAssociatedPrimeStacks S (N ⊗[R] M) q) :
    q + (IsLocalRing.maximalIdeal R).map (algebraMap R S) ≠ ⊤ := by
  classical
  obtain ⟨T, hTindep, hTtop, hTfp⟩ :=
    Module.exists_sSupIndep_finitePresentation_of_countable_span_of_mittagLeffler
      R N hcg ((isMittagLeffler_def_iff R N).mp hML)
  exact associatedPrime_add_map_maximalIdeal_ne_top_of_directSum_finite
    R S N _ (fun i : { i : Submodule R N // i ∈ T } => i.1)
    (fun i => by
      let _ : Module.FinitePresentation R i.1 := hTfp i.1 i.2
      infer_instance)
    (LinearEquiv.ofBijective
      (DirectSum.coeLinearMap fun i : { i : Submodule R N // i ∈ T } => (i.1 : Submodule R N))
      (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
        ((sSupIndep_iff T).1 hTindep) ((sSup_eq_iSup' T).symm.trans hTtop))).symm M q hq

end Stacks.PureModules
