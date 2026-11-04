module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.MittagLeffler.Projective
public import StacksFrontier.LinearAlgebra.Matrix.DeterminantalRank
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Functoriality
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs
public import StacksFrontier.RingTheory.Localization.Glueing.Functions
public import StacksFrontier.RingTheory.SquareZeroQuotient
public import StacksFrontier.RingTheory.UniversallyExact

/-!
# Auto-associated rings

A local ring is auto-associated when its maximal ideal is weakly associated to the ring itself.
Such a ring has the property (P) that every proper finitely generated ideal has nonzero
annihilator, and that property is exactly what characterizes the rings over which every injective
map of projective modules is universally injective.

## Main definitions

* `IsAutoAssociated`: the maximal ideal of a local ring is weakly associated to the ring.

## Main results

* `annihilator_ne_bot_of_isAutoAssociated`: an auto-associated ring has property (P).
* `universallyInjective_iff_injective_of_projective`: over a ring with property (P), an injective
  map of projective modules is universally injective.
* `annihilator_projective_splitting_tfae`: property (P) is equivalent to that statement and to its
  finite-projective form.
* `exists_universallyInjective_nonSplit_freeModule_endomorphism`: property (P) does not force
  injective maps of free modules to split.
* `subsingleton_dual_quotient_range_of_injective`: the dual of the cokernel of an injective
  square matrix map vanishes.

## References

* [Stacks Project, Tag 05GL](https://stacks.math.columbia.edu/tag/05GL)
-/

@[expose] public section

universe u v w

open Stacks.SquareZero

/-- **Stacks 05GM.** A commutative ring is *auto-associated* if it is local and its maximal
ideal is weakly associated to the ring as a module over itself. -/
@[stacks 05GM]
def IsAutoAssociated (R : Type u) [CommRing R] : Prop :=
  ∃ _ : IsLocalRing R,
    IsWeaklyAssociatedPrime R R (IsLocalRing.maximalIdeal R)

/-- **Stacks 05GN.** Every proper finitely generated ideal in an auto-associated ring has a
nonzero annihilator. -/
@[stacks 05GN]
theorem annihilator_ne_bot_of_isAutoAssociated {R : Type u} [CommRing R]
    (hR : IsAutoAssociated R) (I : Ideal R) (hI : I.FG) (hI_ne : I ≠ ⊤) :
    I.annihilator ≠ ⊥ := by
  obtain ⟨localR, x, hx⟩ := hR
  let _ : IsLocalRing R := localR
  obtain ⟨n, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have hx_ne : x ≠ 0 := by
    intro hx0
    subst x
    have hone : (1 : R) ∈ IsLocalRing.maximalIdeal R := hx.le (by
      rw [Submodule.mem_annihilator_span_singleton]
      simp)
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      ((IsLocalRing.maximalIdeal R).eq_top_iff_one.mpr hone)
  have hpower : ∀ i, ∃ k : ℕ, (f i) ^ k * x = 0 := by
    intro i
    have hfiI : f i ∈ I := by
      rw [← hf]
      exact Submodule.subset_span (Set.mem_range_self i)
    have hfiMax : f i ∈ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal hI_ne hfiI
    have hfiRad : f i ∈ (R ∙ x).annihilator.radical := by
      rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
      intro q hq
      exact hx.2 ⟨hq.2, hq.1⟩ (IsLocalRing.le_maximalIdeal hq.2.ne_top) hfiMax
    obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp hfiRad
    exact ⟨k, (Submodule.mem_annihilator_span_singleton x _).mp hk⟩
  have hLambda : ¬ Function.Injective (bigLambda (M := R) n f) := by
    intro hinj
    apply hx_ne
    apply hinj
    funext i
    simp only [bigLambda, LinearMap.pi_apply, map_zero]
    rw [← LinearMap.mem_ker, mem_ker_lambdaMap_iff]
    exact hpower i
  have hPhi : ¬ Function.Injective (bigPhi (M := R) n f) :=
    fun h => hLambda ((bigLambda_injective_iff_bigPhi_injective n f).mpr h)
  simp only [Function.Injective, not_forall] at hPhi
  push Not at hPhi
  obtain ⟨a, b, habPhi, hab⟩ := hPhi
  intro hbot
  have hy_mem : a - b ∈ I.annihilator := by
    rw [← hf, Submodule.mem_annihilator_span]
    intro g
    obtain ⟨i, hi⟩ := g.property
    rw [← hi]
    have hi := congrFun habPhi i
    simpa only [bigPhi, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul, mul_sub, sub_eq_zero, mul_comm] using hi
  rw [hbot] at hy_mem
  exact sub_ne_zero.mpr hab ((Submodule.mem_bot R).mp hy_mem)

section
open LinearMap

private lemma split_of_injective_from_rankOne
    {R : Type u} [CommRing R]
    (hR : ∀ I : Ideal R, I.FG → I ≠ ⊤ → I.annihilator ≠ ⊥)
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (f : R →ₗ[R] M) (hf : Function.Injective f) :
    ∃ p : M →ₗ[R] R, p ∘ₗ f = LinearMap.id := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  let a : M →₀ R := s (f 1)
  let I : Ideal R := Ideal.span (Set.range a)
  have hIfg : I.FG := by
    apply Submodule.fg_span
    refine ((a.support.finite_toSet.image a).insert 0).subset ?_
    rintro x ⟨i, rfl⟩
    by_cases hi : i ∈ a.support
    · exact Set.mem_insert_iff.mpr (.inr ⟨i, hi, rfl⟩)
    · exact Set.mem_insert_iff.mpr (.inl (by simpa using hi))
  have hItop : I = ⊤ := by
    by_contra hI
    have hAnn := hR I hIfg hI
    rw [Submodule.ne_bot_iff] at hAnn
    obtain ⟨r, hrI, hr0⟩ := hAnn
    have hra : r • a = 0 := by
      ext i
      simpa [Finsupp.smul_apply, smul_eq_mul, mul_comm] using
        Submodule.mem_annihilator.mp hrI (a i) (Ideal.subset_span (Set.mem_range_self i))
    have hrfa : r • f 1 = 0 := by
      apply hs.injective
      simpa [a] using hra
    refine hr0 (hf ?_)
    rw [show r = r • (1 : R) by simp, map_smul]
    simpa using hrfa
  have hone : (1 : R) ∈ Ideal.span (Set.range a) := by simp [I, hItop]
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp.mp hone)
  let q : (M →₀ R) →ₗ[R] R :=
    c.sum fun i ci ↦ ci • (Finsupp.lapply i : (M →₀ R) →ₗ[R] R)
  refine ⟨q ∘ₗ s, ?_⟩
  apply LinearMap.ext
  intro r
  simp only [comp_apply, id_apply, q]
  have hsfr : s (f r) = r • a := by
    calc
      s (f r) = s (f (r • (1 : R))) := by simp
      _ = s (r • f 1) := by rw [map_smul]
      _ = r • s (f 1) := by rw [map_smul]
      _ = r • a := rfl
  rw [hsfr]
  simpa [Finsupp.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
    congrArg (r * ·) hc

set_option maxHeartbeats 800000 in
-- The finite-rank induction normalizes nested linear maps and finsupp sums.
private lemma split_of_injective_from_fin
    {R : Type u} [CommRing R]
    (hR : ∀ I : Ideal R, I.FG → I ≠ ⊤ → I.annihilator ≠ ⊥)
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (n : ℕ) (f : (Fin n → R) →ₗ[R] M) (hf : Function.Injective f) :
    ∃ p : M →ₗ[R] (Fin n → R), p ∘ₗ f = LinearMap.id := by
  induction n with
  | zero =>
      let p : M →ₗ[R] (Fin 0 → R) := 0
      refine ⟨p, ?_⟩
      ext i
      exact Fin.elim0 i
  | succ n ih =>
      let e := Fin.consLinearEquiv R (fun _ : Fin (n + 1) ↦ R)
      let i : R →ₗ[R] (Fin (n + 1) → R) :=
        e.toLinearMap ∘ₗ LinearMap.inl R R (Fin n → R)
      let j : (Fin n → R) →ₗ[R] (Fin (n + 1) → R) :=
        e.toLinearMap ∘ₗ LinearMap.inr R R (Fin n → R)
      have hfi : Function.Injective (f ∘ₗ i) :=
        hf.comp (e.injective.comp LinearMap.inl_injective)
      obtain ⟨p, hp⟩ := split_of_injective_from_rankOne hR (f ∘ₗ i) hfi
      let a : M := f (i 1)
      let d : M →ₗ[R] M := LinearMap.id - p.smulRight a
      let g : (Fin n → R) →ₗ[R] M := d ∘ₗ f ∘ₗ j
      have hpa : p a = 1 := by simpa [a] using LinearMap.congr_fun hp 1
      have hginj : Function.Injective g := by
        rw [← LinearMap.ker_eq_bot]
        apply le_antisymm
        · intro y hy
          rw [Submodule.mem_bot]
          have hgy : g y = 0 := by simpa [LinearMap.mem_ker] using hy
          have heq : f (j y) = f (i (p (f (j y)))) := by
            have := sub_eq_zero.mp (by simpa [g, d, a] using hgy)
            calc
              f (j y) = p (f (j y)) • a := this
              _ = p (f (j y)) • f (i 1) := rfl
              _ = f (p (f (j y)) • i 1) := by rw [map_smul]
              _ = f (i (p (f (j y)))) := by
                congr 1
                rw [← i.map_smul]
                simp
          have hij : j y = i (p (f (j y))) := hf heq
          have := e.injective hij
          simpa [i, j] using congrArg Prod.snd this
        · exact bot_le
      obtain ⟨q, hq⟩ := ih g hginj
      let tail : M →ₗ[R] (Fin n → R) := q ∘ₗ d
      let first : M →ₗ[R] R := p - p ∘ₗ f ∘ₗ j ∘ₗ tail
      let ret : M →ₗ[R] (Fin (n + 1) → R) := e.toLinearMap ∘ₗ LinearMap.prod first tail
      refine ⟨ret, ?_⟩
      apply LinearMap.ext
      intro x
      obtain ⟨z, rfl⟩ := e.surjective x
      obtain ⟨r, y⟩ := z
      have hqg := LinearMap.congr_fun hq y
      simp only [comp_apply, id_apply] at hqg ⊢
      have hdecomp : f (e (r, y)) = r • a + f (j y) := by
        rw [show e (r, y) = r • i 1 + j y by apply e.symm.injective; simp [i, j], map_add,
          map_smul]
      apply e.symm.injective
      have hda : d a = 0 := by simp [d, hpa]
      have hdjy : q (d (f (j y))) = y := by simpa [g] using hqg
      simp [ret, first, tail, hdecomp, hpa, hda, hdjy]

/-- A map out of a module splits as soon as its precomposition with an equivalence does. -/
private lemma split_of_equiv_comp {R : Type u} [CommRing R]
    {N N' M : Type*} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    [AddCommGroup M] [Module R M] (e : N ≃ₗ[R] N') (f : N →ₗ[R] M)
    (h : ∃ p : M →ₗ[R] N', p ∘ₗ (f ∘ₗ e.symm.toLinearMap) = LinearMap.id) :
    ∃ p : M →ₗ[R] N, p ∘ₗ f = LinearMap.id := by
  obtain ⟨p, hp⟩ := h
  refine ⟨e.symm.toLinearMap ∘ₗ p, LinearMap.ext fun x => ?_⟩
  simpa using congrArg e.symm (LinearMap.congr_fun hp (e x))

private lemma split_of_injective_from_fintype
    {R : Type u} [CommRing R]
    (hR : ∀ I : Ideal R, I.FG → I ≠ ⊤ → I.annihilator ≠ ⊥)
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]
    {ι : Type v} [Finite ι]
    (f : (ι → R) →ₗ[R] M) (hf : Function.Injective f) :
    ∃ p : M →ₗ[R] (ι → R), p ∘ₗ f = LinearMap.id := by
  let := Fintype.ofFinite ι
  let e : (ι → R) ≃ₗ[R] (Fin (Fintype.card ι) → R) :=
    LinearEquiv.piCongrLeft R (fun _ : Fin (Fintype.card ι) ↦ R) (Fintype.equivFin ι)
  exact split_of_equiv_comp e f
    (split_of_injective_from_fin hR _ (f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective))

private lemma split_of_injective_from_finiteFinsupp
    {R : Type u} [CommRing R]
    (hR : ∀ I : Ideal R, I.FG → I ≠ ⊤ → I.annihilator ≠ ⊥)
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]
    {ι : Type v} [Finite ι]
    (f : (ι →₀ R) →ₗ[R] M) (hf : Function.Injective f) :
    ∃ p : M →ₗ[R] (ι →₀ R), p ∘ₗ f = LinearMap.id := by
  let e := Finsupp.linearEquivFunOnFinite R R ι
  exact split_of_equiv_comp e f
    (split_of_injective_from_fintype hR (f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective))

private lemma universallyInjective_from_finsupp
    {R : Type u} [CommRing R]
    (hR : ∀ I : Ideal R, I.FG → I ≠ ⊤ → I.annihilator ≠ ⊥)
    {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]
    {ι : Type v} (f : (ι →₀ R) →ₗ[R] M) (hf : Function.Injective f) :
    ∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (f.rTensor Q) := by
  classical
  intro Q _ _ x₁ x₂ hx
  let x := x₁ - x₂
  have hx0 : f.rTensor Q x = 0 := by simp [x, hx]
  let E : TensorProduct R (ι →₀ R) Q ≃ₗ[R] (ι →₀ Q) :=
    TensorProduct.equivFinsuppOfBasisLeft (Finsupp.basisSingleOne (R := R) (ι := ι))
  let c : ι →₀ Q := E x
  let s : Finset ι := c.support
  let inc : (s →₀ R) →ₗ[R] (ι →₀ R) := Finsupp.lmapDomain R R Subtype.val
  have hinc : Function.Injective inc := by
    intro a b hab
    apply Finsupp.mapDomain_injective Subtype.val_injective
    simpa [inc, Finsupp.lmapDomain_apply] using hab
  let g : (s →₀ R) →ₗ[R] M := f ∘ₗ inc
  obtain ⟨p, hp⟩ := split_of_injective_from_finiteFinsupp hR g (hf.comp hinc)
  let Es : TensorProduct R (s →₀ R) Q ≃ₗ[R] (s →₀ Q) :=
    TensorProduct.equivFinsuppOfBasisLeft
      (Finsupp.basisSingleOne (R := R) (ι := s))
  let cs : s →₀ Q := c.subtypeDomain (fun i ↦ i ∈ s)
  let y : TensorProduct R (s →₀ R) Q := Es.symm cs
  have hfactor : inc.rTensor Q y = x := by
    rw [show y = cs.sum (fun i q ↦ Finsupp.single i 1 ⊗ₜ[R] q) from
      TensorProduct.equivFinsuppOfBasisLeft_symm_apply _ _]
    rw [show x = c.sum (fun i q ↦ Finsupp.single i 1 ⊗ₜ[R] q) by
      calc
        x = E.symm c := by simp [c]
        _ = c.sum (fun i q ↦ Finsupp.single i 1 ⊗ₜ[R] q) :=
          TensorProduct.equivFinsuppOfBasisLeft_symm_apply _ _]
    simpa [inc, cs, c, s, Finsupp.sum, Finsupp.lmapDomain_apply,
      LinearMap.rTensor_tmul] using
      (Finset.sum_attach (E x).support
        (fun i ↦ Finsupp.single i 1 ⊗ₜ[R] (E x) i))
  have hgy : g.rTensor Q y = 0 := by
    rw [LinearMap.rTensor_comp, LinearMap.comp_apply, hfactor]
    exact hx0
  have hleft : p.rTensor Q (g.rTensor Q y) = y := by
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hp]
    simp
  have : y = 0 := by simpa [hgy] using hleft.symm
  have : x = 0 := by rw [← hfactor, this, map_zero]
  exact sub_eq_zero.mp this

/-- **Stacks 05GP.** Over a ring in which every proper finitely generated ideal has a nonzero
annihilator, a homomorphism between projective modules is universally injective if and only if it
is injective. -/
@[stacks 05GP]
theorem universallyInjective_iff_injective_of_projective
    {R : Type u} [CommRing R]
    (hR : ∀ I : Ideal R, I.FG → I ≠ ⊤ → I.annihilator ≠ ⊥)
    {N M : Type v} [AddCommGroup N] [Module R N] [Module.Projective R N]
    [AddCommGroup M] [Module R M] [Module.Projective R M] (f : N →ₗ[R] M) :
    UniversallyInjective f ↔ Function.Injective f := by
  classical
  constructor
  · intro h x y hxy
    let n : N := x - y
    have hfn : f n = 0 := by simp [n, hxy]
    obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R N).out
    let t : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R (_root_.id : N → N)
    let E : TensorProduct R (N →₀ R) N ≃ₗ[R] (N →₀ N) :=
      TensorProduct.equivFinsuppOfBasisLeft (Finsupp.basisSingleOne (R := R) (ι := N))
    have hz (i : N) : (s n) i • i = 0 := by
      have hni : n ⊗ₜ[R] i = 0 := by
        apply h N
        simp [LinearMap.rTensor_tmul, hfn]
      have hsi : s n ⊗ₜ[R] i = 0 := by
        have := congrArg (s.rTensor N) hni
        simpa using this
      have hE := congrArg (fun z : N →₀ N ↦ z i) (congrArg E hsi)
      simpa [E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply] using hE
    have hsum : (s n).sum (fun i a ↦ a • i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hz i
    have hn : n = 0 := by
      calc
        n = t (s n) := (hs n).symm
        _ = (s n).sum (fun i a ↦ a • i) := by
          simp [t, Finsupp.linearCombination_apply]
        _ = 0 := hsum
    exact sub_eq_zero.mp hn
  · intro hf Q _ _
    obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R N).out
    let t : (N →₀ R) →ₗ[R] N := Finsupp.linearCombination R (_root_.id : N → N)
    let g : (N →₀ R) →ₗ[R] (M × (N →₀ R)) :=
      LinearMap.prod (f ∘ₗ t) (LinearMap.id - s ∘ₗ t)
    have hg : Function.Injective g := by
      intro x y hxy
      have hfirst : f (t x) = f (t y) := congrArg Prod.fst hxy
      have htx : t x = t y := hf (by simpa [g] using hfirst)
      have hsecond : x - s (t x) = y - s (t y) := by
        simpa [g] using congrArg Prod.snd hxy
      calc
        x = (x - s (t x)) + s (t x) := by abel
        _ = (y - s (t y)) + s (t y) := by rw [hsecond, htx]
        _ = y := by abel
    have hgs : g ∘ₗ s = (LinearMap.inl R M (N →₀ R)) ∘ₗ f := by
      apply LinearMap.ext
      intro n
      apply Prod.ext
      · show f (t (s n)) = f n
        rw [hs n]
      · show s n - s (t (s n)) = 0
        rw [hs n]
        simp
    have hginj : Function.Injective (g.rTensor Q) :=
      universallyInjective_from_finsupp hR g hg Q
    intro x y hxy
    have hfx : f.rTensor Q (x - y) = 0 := by simp [hxy]
    have hzero : g.rTensor Q (s.rTensor Q (x - y)) = 0 := by
      calc
        g.rTensor Q (s.rTensor Q (x - y)) = (g ∘ₗ s).rTensor Q (x - y) := by
          rw [LinearMap.rTensor_comp]
          rfl
        _ = ((LinearMap.inl R M (N →₀ R)) ∘ₗ f).rTensor Q (x - y) := by
          rw [hgs]
        _ = (LinearMap.inl R M (N →₀ R)).rTensor Q (f.rTensor Q (x - y)) := by
          rw [LinearMap.rTensor_comp]
          rfl
        _ = 0 := by rw [hfx]; simp
    have hsxy : s.rTensor Q (x - y) = 0 := hginj (by simpa using hzero)
    have ht : (t ∘ₗ s : N →ₗ[R] N) = LinearMap.id := by
      ext n
      exact hs n
    have hxy0 : x - y = 0 := by
      have h := congrArg (t.rTensor Q) hsxy
      simpa [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, ht] using h
    exact sub_eq_zero.mp hxy0

end

/-- **Stacks 05GQ.** For a commutative ring `R`, the following are equivalent: every proper
finitely generated ideal has a nonzero annihilator; every injection between projective modules is
universally injective; the cokernel of every injection between finite projective modules is finite
projective; every finite projective submodule of a finite projective module is a direct summand;
and every injection from `R` to a finite-rank free module splits. The quantified module universe
contains the ring universe, so the finite free modules in the last condition can be lifted into
the preceding conditions. -/
@[stacks 05GQ]
theorem annihilator_projective_splitting_tfae {R : Type u} [CommRing R] :
    [ (∀ I : Ideal R, I.FG → I ≠ ⊤ → I.annihilator ≠ ⊥),
      (∀ (N M : Type (max u v)) [AddCommGroup N] [Module R N] [Module.Projective R N]
        [AddCommGroup M] [Module R M] [Module.Projective R M] (f : N →ₗ[R] M),
        Function.Injective f → UniversallyInjective f),
      (∀ (N M : Type (max u v)) [AddCommGroup N] [Module R N] [Module.Finite R N]
        [Module.Projective R N] [AddCommGroup M] [Module R M] [Module.Finite R M]
        [Module.Projective R M] (f : N →ₗ[R] M), Function.Injective f →
        Module.Finite R (M ⧸ LinearMap.range f) ∧ Module.Projective R (M ⧸ LinearMap.range f)),
      (∀ (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module.Finite R M]
        [Module.Projective R M] (N : Submodule R M) [Module.Finite R N]
        [Module.Projective R N], ∃ p : M →ₗ[R] N, p.comp N.subtype = LinearMap.id),
      (∀ (n : ℕ) (f : R →ₗ[R] (Fin n → R)), Function.Injective f →
        ∃ p : (Fin n → R) →ₗ[R] R, p.comp f = LinearMap.id) ].TFAE := by
  classical
  tfae_have 1 → 2 := by
    intro hR N M _ _ _ _ _ _ f hf
    exact (universallyInjective_iff_injective_of_projective hR f).2 hf
  tfae_have 2 → 3 := by
    intro h N M _ _ _ _ _ _ _ _ f hf
    let q := (LinearMap.range f).mkQ
    have hq : Function.Surjective q := Submodule.mkQ_surjective _
    have hex : Function.Exact f q := by
      rw [LinearMap.exact_iff, Submodule.ker_mkQ]
    have hfg : (LinearMap.ker q).FG := by
      rw [Submodule.ker_mkQ, LinearMap.range_eq_map]
      exact (Module.Finite.fg_top (R := R) (M := N)).map f
    let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
    let : Module.FinitePresentation R (M ⧸ LinearMap.range f) :=
      Module.finitePresentation_of_surjective q hq hfg
    exact ⟨Module.Finite.quotient R _, (Module.Projective.iff_split_of_projective q hq).2
      ((hex.split_iff_forall_rTensor_injective hf hq).2 (h N M f hf))⟩
  tfae_have 3 → 4 := by
    intro h M _ _ _ _ N _ _
    obtain ⟨_, hNquot⟩ := h N M N.subtype N.subtype_injective
    rw [Submodule.range_subtype] at hNquot
    let : Module.Projective R (M ⧸ N) := hNquot
    obtain ⟨p, hp⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
    have hex := LinearMap.exact_subtype_mkQ N
    exact ((hex.split_tfae N.subtype_injective N.mkQ_surjective).out 1 2).mp
      (show ∃ p : (M ⧸ N) →ₗ[R] M, N.mkQ.comp p = LinearMap.id from ⟨p, hp⟩)
  tfae_have 4 → 5 := by
    intro h n f hf
    let eM : ULift.{v} (Fin n → R) ≃ₗ[R] (Fin n → R) := ULift.moduleEquiv
    let f' : R →ₗ[R] ULift.{v} (Fin n → R) := eM.symm.toLinearMap.comp f
    have hf' : Function.Injective f' := eM.symm.injective.comp hf
    let N : Submodule R (ULift.{v} (Fin n → R)) := LinearMap.range f'
    let e : R ≃ₗ[R] N := LinearEquiv.ofInjective f' hf'
    let : Module.Finite R N := Module.Finite.equiv e
    let : Module.Projective R N := Module.Projective.of_equiv' e
    obtain ⟨p, hp⟩ := h (ULift.{v} (Fin n → R)) N
    refine ⟨e.symm.toLinearMap.comp (p.comp eM.symm.toLinearMap), LinearMap.ext fun x => ?_⟩
    simpa [e, N, f', eM] using congrArg e.symm (LinearMap.congr_fun hp (e x))
  tfae_have 5 → 1 := by
    intro h I hI hIne hbot
    obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
    let f : R →ₗ[R] (Fin n → R) := LinearMap.pi fun i => LinearMap.mulLeft R (s i)
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot]
      apply le_bot_iff.mp
      intro x hx
      have hxa : x ∈ I.annihilator := by
        rw [← hs, Submodule.mem_annihilator_span]
        rintro ⟨_, i, rfl⟩
        simpa [f, smul_eq_mul, mul_comm] using congrFun (show f x = 0 from hx) i
      rw [hbot] at hxa
      exact hxa
    obtain ⟨p, hp⟩ := h n f hf
    apply hIne
    rw [← hs, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]
    refine ⟨fun i => p (Pi.single i 1), ?_⟩
    have hp1 := LinearMap.congr_fun hp 1
    have hf1 : f 1 = fun i => s i := by
      ext i
      simp [f, LinearMap.pi_apply, LinearMap.mulLeft_apply]
    rw [LinearMap.comp_apply, hf1, LinearMap.id_apply] at hp1
    have hv : (fun i => s i) = ∑ i, s i • Pi.single i 1 := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    have hpv : p (fun i => s i) = ∑ i, p (Pi.single i 1) * s i := by
      rw [hv, map_sum]
      simp [mul_comm]
    rw [← hpv]
    exact hp1
  tfae_finish

private noncomputable def triangularShift (R : Type*) [CommRing R] (x : ℕ → R) :
    (ℕ →₀ R) →ₗ[R] (ℕ →₀ R) :=
  Finsupp.linearCombination R
    (fun i => Finsupp.single i 1 - x i • Finsupp.single (i + 1) 1)

private theorem triangularShift_single {R : Type*} [CommRing R] (x : ℕ → R) (i : ℕ) :
    triangularShift R x (Finsupp.single i 1) =
      Finsupp.single i 1 - x i • Finsupp.single (i + 1) 1 := by
  simp [triangularShift]

private theorem lapply_zero_comp_triangularShift {R : Type*} [CommRing R] (x : ℕ → R) :
    (Finsupp.lapply 0).comp (triangularShift R x) = Finsupp.lapply 0 := by
  classical
  apply Finsupp.lhom_ext
  intro j b
  simp [triangularShift, Finsupp.linearCombination_single, Finsupp.single_apply]

private theorem lapply_succ_comp_triangularShift {R : Type*} [CommRing R]
    (x : ℕ → R) (i : ℕ) :
    (Finsupp.lapply (i + 1)).comp (triangularShift R x) =
      Finsupp.lapply (i + 1) - x i • Finsupp.lapply i := by
  classical
  apply Finsupp.lhom_ext
  intro j b
  by_cases hj : j = i
  · subst j
    simp [triangularShift, Finsupp.linearCombination_single, mul_comm]
  by_cases hj' : j = i + 1
  · subst j
    simp [triangularShift, Finsupp.linearCombination_single]
  simp [triangularShift, Finsupp.linearCombination_single, hj, hj']

private theorem triangularShift_apply_zero {R : Type*} [CommRing R]
    (x : ℕ → R) (a : ℕ →₀ R) :
    (triangularShift R x a) 0 = a 0 :=
  LinearMap.congr_fun (lapply_zero_comp_triangularShift x) a

private theorem triangularShift_apply_succ {R : Type*} [CommRing R]
    (x : ℕ → R) (a : ℕ →₀ R) (i : ℕ) :
    (triangularShift R x a) (i + 1) = a (i + 1) - x i * a i :=
  LinearMap.congr_fun (lapply_succ_comp_triangularShift x i) a

private theorem triangularShift_injective {R : Type*} [CommRing R]
    (x : ℕ → R) : Function.Injective (triangularShift R x) := by
  refine (injective_iff_map_eq_zero _).mpr fun a ha => Finsupp.ext fun i => ?_
  induction i with
  | zero =>
      have h := triangularShift_apply_zero x a
      rw [ha] at h
      simpa using h.symm
  | succ i ih =>
      have h := triangularShift_apply_succ x a i
      rw [ha, ih] at h
      simpa using h.symm

/-- Tensoring the triangular shift preserves the recurrence determining its input. -/
private theorem triangularShift_universallyInjective {R : Type*} [CommRing R]
    (x : ℕ → R) : UniversallyInjective (triangularShift R x) := by
  intro Q _ _
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hcoord : ∀ i : ℕ, ((Finsupp.lapply i : (ℕ →₀ R) →ₗ[R] R).rTensor Q) a = 0 := by
    intro i
    induction i with
    | zero =>
        have h := congrArg ((Finsupp.lapply 0 : (ℕ →₀ R) →ₗ[R] R).rTensor Q) ha
        rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
          lapply_zero_comp_triangularShift] at h
        simpa using h
    | succ i ih =>
        have h := congrArg ((Finsupp.lapply (i + 1) : (ℕ →₀ R) →ₗ[R] R).rTensor Q) ha
        rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
          lapply_succ_comp_triangularShift, LinearMap.rTensor_sub, LinearMap.rTensor_smul] at h
        simpa [ih] using h
  apply (TensorProduct.finsuppLeft R R R Q ℕ).injective
  ext i
  simpa only [TensorProduct.finsuppLeft_apply, map_zero, Finsupp.zero_apply] using hcoord i

private theorem triangularShift_linearIndependent {R : Type*} [CommRing R]
    [Nontrivial R] (x : ℕ → R) (n : ℕ) :
    LinearIndependent R (fun i : Fin n =>
      triangularShift R x (Finsupp.single i 1)) := by
  have hb : LinearIndependent R
      (fun i : ℕ => (Finsupp.single i (1 : R) : ℕ →₀ R)) :=
    Finsupp.linearIndependent_single_one R ℕ
  have hc := hb.comp (fun i : Fin n => (i : ℕ)) Fin.val_injective
  exact hc.map' (triangularShift R x)
    (LinearMap.ker_eq_bot.mpr (triangularShift_injective x))

private theorem initialProduct_ne_zero (k : Type u) [Field k] (n : ℕ) :
    (∏ i ∈ Finset.range n,
      (Ideal.Quotient.mk (sqIdeal k) (MvPolynomial.X i) : S k)) ≠ 0 := by
  let d : ℕ →₀ ℕ := Finsupp.indicator (Finset.range n) (fun _ _ => 1)
  have hd : IsSqFree d := by
    intro i
    simp only [d, Finsupp.indicator_apply]
    split_ifs <;> omega
  intro hzero
  have hmem : (∏ i ∈ Finset.range n, (MvPolynomial.X i : MvPolynomial ℕ k)) ∈
      sqIdeal k := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_prod] using hzero
  have hcoeff := mem_sqIdeal_iff.mp hmem d hd
  have hpoly : (∏ i ∈ Finset.range n, (MvPolynomial.X i : MvPolynomial ℕ k)) =
      MvPolynomial.monomial d 1 := by
    simpa only [pow_one] using
      (MvPolynomial.prod_X_pow (fun _ : ℕ => 1) (Finset.range n) :
        ∏ i ∈ Finset.range n, (MvPolynomial.X i : MvPolynomial ℕ k) ^ 1 =
          MvPolynomial.monomial d 1)
  rw [hpoly, MvPolynomial.coeff_monomial, ite_eq_left rfl] at hcoeff
  exact one_ne_zero hcoeff

private theorem squareZero_isAutoAssociated (k : Type u) [Field k] :
    IsAutoAssociated (S k) := by
  let : IsLocalRing (S k) := isLocalRing k
  refine ⟨inferInstance, ?_⟩
  have hm : nilradical (S k) = IsLocalRing.maximalIdeal (S k) :=
    (nilradical_eq_ker_aug k).trans
      (IsLocalRing.ker_eq_maximalIdeal (aug k).toRingHom (aug_surjective k))
  have ha : ((S k ∙ (1 : S k)).annihilator : Ideal (S k)) = ⊥ := by
    ext r
    simp only [Submodule.mem_annihilator_span_singleton, smul_eq_mul, mul_one,
      Ideal.mem_bot]
  show ∃ s : S k,
    IsLocalRing.maximalIdeal (S k) ∈ (S k ∙ s).annihilator.minimalPrimes
  refine ⟨1, ?_⟩
  rw [ha, ← Ideal.radical_minimalPrimes]
  show IsLocalRing.maximalIdeal (S k) ∈ (nilradical (S k)).minimalPrimes
  rw [hm, Ideal.minimalPrimes_eq_subsingleton_self]
  rfl

/-- The triangular shift cannot hit the first basis vector when every initial product of its
coefficients is nonzero. -/
private theorem triangularShift_not_surjective {R : Type*} [CommRing R]
    (x : ℕ → R) (ν : (ℕ →₀ R) →ₗ[R] (ℕ →₀ R))
    (hzero : ∀ a, (ν a) 0 = a 0)
    (hsucc : ∀ a i, (ν a) (i + 1) = a (i + 1) - x i * a i)
    (hprod : ∀ n : ℕ, (∏ i ∈ Finset.range n, x i) ≠ 0) :
    ¬ Function.Surjective ν := by
  intro hsurj
  obtain ⟨a, ha⟩ := hsurj (Finsupp.single 0 (1 : R))
  have ha0 : a 0 = 1 := by
    rw [← hzero a, ha]
    simp
  have harec (i : ℕ) : a (i + 1) = x i * a i := by
    have hi := congrArg (fun v : ℕ →₀ R => v (i + 1)) ha
    rw [hsucc] at hi
    simpa [sub_eq_zero] using hi
  have haprod (n : ℕ) : a n = ∏ i ∈ Finset.range n, x i := by
    induction n with
    | zero => simpa using ha0
    | succ n ih => simp [harec n, ih, Finset.prod_range_succ, mul_comm]
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset a.support
  have han : a n = 0 := Finsupp.notMem_support_iff.mp hn
  exact hprod n (haprod n ▸ han)

/-- A triangular shift with square-zero coefficients and nonzero initial products has no
left inverse. -/
private theorem triangularShift_not_split {R : Type*} [CommRing R]
    (x : ℕ → R) (ν : (ℕ →₀ R) →ₗ[R] (ℕ →₀ R))
    (hν : ∀ i, ν (Finsupp.single i 1) =
      Finsupp.single i 1 - x i • Finsupp.single (i + 1) 1)
    (hsq : ∀ i, x i ^ 2 = 0)
    (hprod : ∀ n : ℕ, (∏ i ∈ Finset.range n, x i) ≠ 0) :
    ¬ ∃ p : (ℕ →₀ R) →ₗ[R] (ℕ →₀ R), p.comp ν = LinearMap.id := by
  classical
  rintro ⟨p, hp⟩
  let e : ℕ → ℕ →₀ R := fun i => Finsupp.single i 1
  have hrec (i : ℕ) : p (e i) = e i + x i • p (e (i + 1)) := by
    have hi := LinearMap.congr_fun hp (e i)
    change p (ν (e i)) = e i at hi
    rw [show ν (e i) = e i - x i • e (i + 1) from hν i] at hi
    simpa only [map_sub, map_smul, sub_eq_iff_eq_add] using hi
  have hiter (n : ℕ) :
      p (e 0) =
        (∑ i ∈ Finset.range n, (∏ j ∈ Finset.range i, x j) • e i) +
          (∏ j ∈ Finset.range n, x j) • p (e n) := by
    induction n with
    | zero => simp [e]
    | succ n ih =>
        rw [ih, hrec n, smul_add, smul_smul, Finset.sum_range_succ,
          Finset.prod_range_succ]
        simp only [add_assoc]
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset (p (e 0)).support
  have hcoord : (p (e 0)) n = 0 := Finsupp.notMem_support_iff.mp hn
  have hzero : (∑ i ∈ Finset.range n, (∏ j ∈ Finset.range i, x j) • e i) n = 0 := by
    show (Finsupp.lapply n : (ℕ →₀ R) →ₗ[R] R)
      (∑ i ∈ Finset.range n, (∏ j ∈ Finset.range i, x j) • e i) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    have hin : i ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hi)
    simp [e, hin]
  have hmain := congrArg (fun a : ℕ →₀ R => a n) (hiter n)
  rw [hcoord, Finsupp.add_apply, hzero, zero_add, Finsupp.smul_apply] at hmain
  have hrecn := congrArg (fun a : ℕ →₀ R => a n) (hrec n)
  simp only [Finsupp.add_apply, Finsupp.smul_apply] at hrecn
  have he : (e n) n = (1 : R) := by simp [e]
  rw [he] at hrecn
  have hlast : (∏ j ∈ Finset.range n, x j) * x n = 0 := by
    rw [hrecn] at hmain
    have hmul := congrArg (fun r : R => r * x n) hmain
    simp only [smul_eq_mul, zero_mul] at hmul
    ring_nf at hmul
    rw [hsq n] at hmul
    simp only [mul_zero, zero_mul, add_zero] at hmul
    exact hmul.symm
  exact hprod (n + 1) (by simpa [Finset.prod_range_succ] using hlast)

/-- A nilpotent ideal in a nonzero ring has a nonzero annihilator. -/
private theorem annihilator_ne_bot_of_isNilpotent {R : Type*} [CommRing R] [Nontrivial R]
    (J : Ideal R) (hJ : IsNilpotent J) : J.annihilator ≠ ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  induction n with
  | zero =>
      simp at hn
  | succ n ih =>
      by_cases hpow : J ^ n = ⊥
      · exact ih hpow
      · intro hann
        have hle : J ^ n ≤ J.annihilator := by
          intro r hr
          apply Submodule.mem_annihilator.mpr
          intro s hs
          have hmul : r * s ∈ J ^ (n + 1) := by
            rw [pow_succ]
            exact Ideal.mul_mem_mul hr hs
          rw [hn] at hmul
          exact Ideal.mem_bot.mp hmul
        exact hpow (eq_bot_iff.mpr (hle.trans (le_of_eq hann)))

private theorem squareZero_finiteIdeal_annihilator_ne_bot (k : Type u) [Field k] :
    ∀ J : Ideal (S k), J.FG → J ≠ ⊤ → J.annihilator ≠ ⊥ := by
  let : IsLocalRing (S k) := isLocalRing k
  intro J hfg hproper
  have hle : J ≤ nilradical (S k) := by
    rw [nilradical_eq_ker_aug]
    exact (IsLocalRing.le_maximalIdeal hproper).trans_eq
      ((IsLocalRing.ker_eq_maximalIdeal (aug k).toRingHom (aug_surjective k)).symm)
  exact annihilator_ne_bot_of_isNilpotent J
    ((Ideal.FG.isNilpotent_iff_le_nilradical hfg).mpr hle)

/-- The cokernel of a universally injective map into a flat module is flat. -/
private theorem flat_cokernel_of_universallyInjective {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Flat R N] (f : M →ₗ[R] N) (hf : UniversallyInjective f) :
    Module.Flat R (N ⧸ LinearMap.range f) := by
  have hsub : ∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
      Function.Injective ((LinearMap.range f).subtype.rTensor Q) := by
    intro Q _ _ a b hab
    obtain ⟨a', rfl⟩ := LinearMap.rTensor_surjective Q f.surjective_rangeRestrict a
    obtain ⟨b', rfl⟩ := LinearMap.rTensor_surjective Q f.surjective_rangeRestrict b
    have hcomp : (LinearMap.range f).subtype.comp f.rangeRestrict = f :=
      LinearMap.ext fun _ => rfl
    have hν : (f.rTensor Q) a' = (f.rTensor Q) b' := by
      rw [← hcomp, LinearMap.rTensor_comp]
      exact hab
    have h := hf Q hν
    exact congrArg (f.rangeRestrict.rTensor Q) h
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro A B _ _ _ _ g hg
  exact lTensor_injective_of_exact_of_exact_of_rTensor_injective
    (LinearMap.exact_subtype_mkQ (LinearMap.range f))
    (Submodule.mkQ_surjective (LinearMap.range f))
    (LinearMap.exact_map_mkQ_range g)
    (Submodule.mkQ_surjective (LinearMap.range g))
    (hsub (B ⧸ LinearMap.range g))
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)

private theorem triangularShift_rTensor_eq_id {R : Type*} [CommRing R]
    (x : ℕ → R) {Q : Type*} [AddCommGroup Q] [Module R Q]
    (hx : ∀ i (q : Q), x i • q = 0) :
    (triangularShift R x).rTensor Q = LinearMap.id := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | tmul a q =>
      induction a using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb =>
          simp only [LinearMap.rTensor_tmul, map_add, TensorProduct.add_tmul,
            LinearMap.id_apply] at ha hb ⊢
          rw [ha, hb]
      | single i r =>
          have hs : (Finsupp.single i r : ℕ →₀ R) =
              r • Finsupp.single i 1 := by simp
          rw [LinearMap.rTensor_tmul, hs, map_smul,
            triangularShift_single, smul_sub, TensorProduct.smul_tmul,
            TensorProduct.sub_tmul, TensorProduct.smul_tmul]
          rw [smul_comm r (x i) (Finsupp.single (i + 1) (1 : R)),
            TensorProduct.smul_tmul (x i), hx i q]
          simp

/-- An injective linear map with projective cokernel admits a left inverse. -/
private theorem split_of_projective_cokernel {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Injective f)
    (hproj : Module.Projective R (N ⧸ LinearMap.range f)) :
    ∃ p : N →ₗ[R] M, p.comp f = LinearMap.id := by
  let q : N →ₗ[R] N ⧸ LinearMap.range f := (LinearMap.range f).mkQ
  have := hproj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id
    (Submodule.mkQ_surjective _)
  let v : N →ₗ[R] N := LinearMap.id - s.comp q
  let t : N →ₗ[R] LinearMap.range f :=
    v.codRestrict (LinearMap.range f) (by
      intro y
      apply (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mp
      have hsy := LinearMap.congr_fun hs (q y)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsy
      show q (v y) = 0
      dsimp only [v]
      simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub]
      rw [hsy]
      exact sub_self _)
  let e : M ≃ₗ[R] LinearMap.range f := LinearEquiv.ofBijective f.rangeRestrict
    ⟨(fun a b hab => hf (congrArg Subtype.val hab)), f.surjective_rangeRestrict⟩
  refine ⟨e.symm.toLinearMap.comp t, ?_⟩
  apply LinearMap.ext
  intro a
  have hq : q (f a) = 0 := (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
  have ht : t (f a) = f.rangeRestrict a := by
    apply Subtype.ext
    show v (f a) = f a
    dsimp only [v]
    simp [hq]
  show e.symm (t (f a)) = a
  rw [ht]
  exact e.left_inv a

/-- **Stacks 05GR.** Let `R = k[x₁, x₂, …]/(xᵢ²)`. The endomorphism of the countable free
`R`-module given on basis vectors by `eᵢ ↦ eᵢ - xᵢ eᵢ₊₁` is injective and universally
injective, but is neither surjective nor split. After specializing every variable to zero it
becomes an isomorphism. Its cokernel is countably generated and flat, but is not projective and
not Mittag--Leffler. The ring `R` is auto-associated and satisfies the annihilator condition of
Stacks 05GQ. -/
@[stacks 05GR]
theorem exists_universallyInjective_nonSplit_freeModule_endomorphism
    (k : Type u) [Field k] :
    let P := MvPolynomial ℕ k
    let I : Ideal P := Ideal.span (Set.range (fun i : ℕ ↦ MvPolynomial.X i ^ 2))
    let R := P ⧸ I
    let x : ℕ → R := fun i ↦ Ideal.Quotient.mk I (MvPolynomial.X i)
    ∃ ν : (ℕ →₀ R) →ₗ[R] (ℕ →₀ R),
      (∀ i, ν (Finsupp.single i 1) =
        Finsupp.single i 1 - x i • Finsupp.single (i + 1) 1) ∧
      (∀ n : ℕ, LinearIndependent R (fun i : Fin n ↦ ν (Finsupp.single i 1))) ∧
      IsAutoAssociated R ∧
      (∀ J : Ideal R, J.FG → J ≠ ⊤ → J.annihilator ≠ ⊥) ∧
      Function.Injective ν ∧
      UniversallyInjective ν ∧
      (∃ ε : R →ₐ[k] k, (∀ i, ε (x i) = 0) ∧
        letI := ε.toRingHom.toAlgebra
        Function.Bijective (ν.rTensor k)) ∧
      ¬ Function.Surjective ν ∧
      ¬ (∃ p : (ℕ →₀ R) →ₗ[R] (ℕ →₀ R), p.comp ν = LinearMap.id) ∧
      Module.Flat R ((ℕ →₀ R) ⧸ LinearMap.range ν) ∧
      Module.CountablyGenerated R ((ℕ →₀ R) ⧸ LinearMap.range ν) ∧
      ¬ Module.Projective R ((ℕ →₀ R) ⧸ LinearMap.range ν) ∧
      ¬ IsMittagLeffler.{u, u, u, u, u} R ((ℕ →₀ R) ⧸ LinearMap.range ν) := by
  let x : ℕ → S k := fun i => Ideal.Quotient.mk (sqIdeal k) (MvPolynomial.X i)
  let ν := triangularShift (S k) x
  have hprod : ∀ n : ℕ, (∏ i ∈ Finset.range n, x i) ≠ 0 :=
    initialProduct_ne_zero k
  have hsq : ∀ i, x i ^ 2 = 0 := squareZero_generator k
  have hinj : Function.Injective ν := triangularShift_injective x
  have huni : UniversallyInjective ν := triangularShift_universallyInjective x
  have hcg : Module.CountablyGenerated (S k)
      ((ℕ →₀ S k) ⧸ LinearMap.range ν) := by
    have hfree : Module.CountablyGenerated (S k) (ℕ →₀ S k) := by
      refine ⟨Set.range (fun i : ℕ => Finsupp.single i (1 : S k)),
        Set.countable_range _, ?_⟩
      rw [← Set.image_univ, ← Finsupp.supported_eq_span_single]
      simp
    exact Module.CountablyGenerated.of_surjective (LinearMap.range ν).mkQ
      (Submodule.mkQ_surjective _) hfree
  have hflat := flat_cokernel_of_universallyInjective ν huni
  have hsplit := triangularShift_not_split x ν (triangularShift_single x) hsq hprod
  have hproj : ¬ Module.Projective (S k) ((ℕ →₀ S k) ⧸ LinearMap.range ν) :=
    fun hp => hsplit (split_of_projective_cokernel ν hinj hp)
  refine ⟨ν, triangularShift_single x,
    triangularShift_linearIndependent x, squareZero_isAutoAssociated k,
    squareZero_finiteIdeal_annihilator_ne_bot k, hinj, huni, ?_, ?_, hsplit,
    hflat, hcg, hproj, fun h => hproj
      (Module.Flat.projective_of_isMittagLeffler_of_countablyGenerated (S k) _ h hcg)⟩
  · refine ⟨aug k, fun i => (aug_mk k (MvPolynomial.X i)).trans (by simp), ?_⟩
    let := (aug k).toRingHom.toAlgebra
    have hx : ∀ i (q : k), x i • q = 0 := by
      intro i q
      show (aug k) (x i) * q = 0
      rw [aug_mk]
      simp
    show Function.Bijective ((triangularShift (S k) x).rTensor k)
    rw [triangularShift_rTensor_eq_id x hx]
    exact Function.bijective_id
  · exact triangularShift_not_surjective x ν
      (triangularShift_apply_zero x) (triangularShift_apply_succ x) hprod

private theorem injective_dualMap_of_injective
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) : Function.Injective φ.dualMap := by
  classical
  let b := Module.Free.chooseBasis R M
  let ι := Module.Free.ChooseBasisIndex R M
  let : Fintype ι := Fintype.ofFinite ι
  let A : Matrix ι ι R := LinearMap.toMatrix b b φ
  have hA : Function.Injective A.mulVec := by
    intro x y hxy
    apply b.equivFun.symm.injective
    apply hφ
    apply b.equivFun.injective
    have hx := LinearMap.toMatrix_mulVec_repr b b φ (b.equivFun.symm x)
    have hy := LinearMap.toMatrix_mulVec_repr b b φ (b.equivFun.symm y)
    show ⇑(b.repr (φ (b.equivFun.symm x))) = ⇑(b.repr (φ (b.equivFun.symm y)))
    rw [← hx, ← hy, show ⇑(b.repr (b.equivFun.symm x)) = x from b.equivFun.apply_symm_apply x,
      show ⇑(b.repr (b.equivFun.symm y)) = y from b.equivFun.apply_symm_apply y]
    exact hxy
  have hAt : Function.Injective A.transpose.mulVec := by
    rw [Matrix.mulVec_injective_iff]
    exact (Matrix.Nonsingular.of_linearIndependent_col
      (Matrix.mulVec_injective_iff.mp hA)).linearIndependent_row
  intro f g hfg
  apply b.dualBasis.equivFun.injective
  apply hAt
  have hf := LinearMap.toMatrix_mulVec_repr b.dualBasis b.dualBasis φ.dualMap f
  have hg := LinearMap.toMatrix_mulVec_repr b.dualBasis b.dualBasis φ.dualMap g
  have hmatrix : LinearMap.toMatrix b.dualBasis b.dualBasis φ.dualMap = A.transpose := by
    show LinearMap.toMatrix b.dualBasis b.dualBasis (Module.Dual.transpose φ) =
      (LinearMap.toMatrix b b φ).transpose
    exact LinearMap.toMatrix_transpose φ
  rw [hmatrix] at hf hg
  show A.transpose.mulVec ⇑(b.dualBasis.repr f) =
    A.transpose.mulVec ⇑(b.dualBasis.repr g)
  rw [hf, hg]
  exact congr_arg (fun h : Module.Dual R M => ⇑(b.dualBasis.repr h)) hfg

/-- **Stacks 0EWY.** The dual of the cokernel of an injective endomorphism of a finite free
module is zero. -/
@[stacks 0EWY]
theorem subsingleton_dual_quotient_range_of_injective
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    Subsingleton (Module.Dual R (M ⧸ LinearMap.range φ)) := by
  refine ⟨fun f g => ?_⟩
  apply LinearMap.dualMap_injective_of_surjective (Submodule.mkQ_surjective _)
  apply injective_dualMap_of_injective φ hφ
  ext x
  show f (Submodule.Quotient.mk (φ x)) = g (Submodule.Quotient.mk (φ x))
  have hx : Submodule.Quotient.mk (φ x) = (0 : M ⧸ LinearMap.range φ) :=
    (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
  rw [hx, map_zero, map_zero]

-- 00MX is proved in `StacksFrontier.LinearAlgebra.Matrix.DeterminantalRank`, whose declarations
-- already carry tag 00MV; only the 00MX registration is owed, and it is recorded here rather
-- than by re-exporting those declarations under new names.
add_to_stacks 00MX "(1) iff (2)"
  Stacks.DeterminantalRank.injective_iff_rank_eq_and_annihilator_eq_bot
add_to_stacks 00MX "(1) iff (3)"
  Stacks.DeterminantalRank.injective_iff_rank_eq_and_contains_nonZeroDivisor
