module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Localization.Integer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement

/-!
# Associated primes of a relative dualizing module

Given a finite-open factorization of a map of Noetherian rings, a prime of the target is
associated to the relative dualizing module exactly when its contraction to the base ring is
associated to the base ring itself. So the associated primes of the relative dualizing module are
precisely the primes lying over associated primes of the base.

## Main results

* `Stacks.Discriminant.mem_associatedPrimes_dualizingModule_iff` characterizes the associated
  primes of the relative dualizing module by contraction to the base ring.

## Implementation notes

The dualizing module is formed from an explicit finite-open factorization. That factorization
already supplies the quasi-finiteness data used in the source, so no separate quasi-finiteness
hypothesis is needed. The characterization is stated pointwise for prime ideals of the target, so
that it can be used in either direction.

The proof reduces to the finite case — where the dual of a finite algebra has the stated
associated primes — by localizing at an element of the intermediate algebra over which the map to
the target is an isomorphism of away localizations. Transporting associated primes along that
isomorphism and along the localization maps is what the auxiliary results below provide.

## References

* [Stacks Project, Tag 0BVD](https://stacks.math.columbia.edu/tag/0BVD)
-/

@[expose] public section

universe u v w

namespace Stacks.Discriminant

open scoped TensorProduct

attribute [local instance] algebraDualModule

private theorem finiteDual_comap_associatedPrimes
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing C] [Module.Finite A C]
    (q : Ideal C) (hq : q ∈ associatedPrimes C (Module.Dual A C)) :
    q.comap (algebraMap A C) ∈ associatedPrimes A A := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hq
  obtain ⟨hqprime, f, hf⟩ := hq
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := C)
  let J : Fin n → Ideal A := fun i => (⊥ : Submodule A A).colon {f (s i)}
  have hsmul (a : A) (x : C) : f (algebraMap A C a * x) = a • f x := by
    rw [← Algebra.smul_def, map_smul]
  have hJ : q.comap (algebraMap A C) = Finset.univ.inf J := by
    ext a
    simp only [Ideal.mem_comap, Finset.inf_univ_eq_iInf, Submodule.mem_iInf]
    constructor
    · intro ha i
      rw [hf] at ha
      have hz : (algebraMap A C a) • f = 0 := Submodule.mem_colon_singleton.mp ha
      have hz' := congrArg (fun g : Module.Dual A C => g (s i)) hz
      have hz'' : f ((algebraMap A C a) * s i) = 0 := by
        simpa [algebraDualModule_smul_apply] using hz'
      show a ∈ (⊥ : Submodule A A).colon {f (s i)}
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      rwa [hsmul] at hz''
    · intro ha
      show (algebraMap A C a) ∈ q
      rw [hf, Submodule.mem_colon_singleton, Submodule.mem_bot]
      refine LinearMap.ext_on_range hs fun i => ?_
      show f ((algebraMap A C a) * s i) = 0
      have hz := ha i
      change a ∈ (⊥ : Submodule A A).colon {f (s i)} at hz
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hz
      rwa [hsmul]
  have hp : (q.comap (algebraMap A C)).IsPrime := hqprime.comap (algebraMap A C)
  obtain ⟨i, -, hJi⟩ :=
    Ideal.eq_inf_of_isPrime_inf (s := Finset.univ) (f := J) (by simpa [hJ] using hp)
  exact (isAssociatedPrime_iff).2 ⟨hp, f (s i), hJ.trans hJi.symm⟩

private noncomputable def fieldDualFunctional
    {K L : Type*} [Field K] [Field L] [Algebra K L] : L →ₗ[K] K := by
  let _ : Module.Free K L := Module.Free.of_divisionRing K L
  let b := Module.Free.chooseBasis K L
  let i : Module.Free.ChooseBasisIndex K L := Classical.choice
    (Module.Free.instNonemptyChooseBasisIndexOfNontrivial K L)
  exact b.coord i

private theorem fieldDualFunctional_ne_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L] :
    fieldDualFunctional (K := K) (L := L) ≠ 0 := by
  let _ : Module.Free K L := Module.Free.of_divisionRing K L
  let b := Module.Free.chooseBasis K L
  let i : Module.Free.ChooseBasisIndex K L := Classical.choice
    (Module.Free.instNonemptyChooseBasisIndexOfNontrivial K L)
  intro h
  have h' := LinearMap.congr_fun h (b i)
  simp [fieldDualFunctional, b, i] at h'

private theorem fieldDualFunctional_comp_lmul_ne_zero
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (ell : L →ₗ[K] K) (hell : ell ≠ 0) (z : L) (hz : z ≠ 0) :
    ell.comp (Algebra.lmul K L z) ≠ 0 := by
  intro h
  apply hell
  ext y
  have h' := LinearMap.congr_fun h (z⁻¹ * y)
  change ell (z * (z⁻¹ * y)) = 0 at h'
  simpa [mul_assoc, hz] using h'

private theorem finite_denominators_clear
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (n : ℕ) (f : Fin n → K) :
    ∃ d : R, d ≠ 0 ∧ ∀ i, ∃ r : R,
      algebraMap R K r = algebraMap R K d * f i := by
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) f
  refine ⟨d.1, mem_nonZeroDivisors_iff_ne_zero.mp d.2, fun i ↦ ?_⟩
  have hi : IsLocalization.IsInteger R (d.1 • f i) := hd i
  change d.1 • f i ∈ (algebraMap R K).rangeS at hi
  rcases hi with ⟨r, hr⟩
  exact ⟨r, by simpa [Algebra.smul_def] using hr⟩

private theorem exists_ne_of_span_eq_top
    {K L C : Type*} [Field K] [Field L] [Algebra K L]
    (φ : C → L) (hspan : Submodule.span K (Set.range φ) = ⊤)
    (f : L →ₗ[K] K) (hf : f ≠ 0) : ∃ c, f (φ c) ≠ 0 := by
  by_contra! h
  exact hf (LinearMap.ext_on_range hspan h)

private theorem fieldFunctional_ann_eq_ker
    {A C K L : Type*} [CommRing A] [CommRing C] [Field K] [Field L]
    [Algebra A C] [Algebra A K] [Algebra A L] [Algebra K L]
    [IsScalarTower A K L]
    [Algebra C L] [IsScalarTower A C L]
    (φ : C →ₐ[A] L) (hspan : Submodule.span K (Set.range φ) = ⊤)
    (ell : L →ₗ[K] K) (hell : ell ≠ 0) :
    {c : C | ∀ x : C, ell (φ (c * x)) = 0} = RingHom.ker φ.toRingHom := by
  ext c
  show (∀ x : C, ell (φ (c * x)) = 0) ↔ φ c = 0
  constructor
  · intro h
    by_contra hc
    have hmul : ell.comp (Algebra.lmul K L (φ c)) ≠ 0 :=
      fieldDualFunctional_comp_lmul_ne_zero ell hell (φ c) hc
    obtain ⟨x, hx⟩ := exists_ne_of_span_eq_top φ hspan _ hmul
    change ell (φ c * φ x) ≠ 0 at hx
    exact hx (by simpa only [map_mul] using h x)
  · intro hc x
    rw [map_mul, hc, zero_mul, ell.map_zero]

/-- A finite extension of domains carries a linear functional whose associated bilinear form is
nondegenerate: there is an `R`-linear map `hD : D →ₗ[R] R` for which the only `z : D` with
`hD (z * y) = 0` for every `y : D` is `z = 0`.

It is built from a nonzero `K`-linear functional on the fraction field `L` of `D`, whose
annihilator ideal is the kernel of `D → L` by `fieldFunctional_ann_eq_ker`, by clearing
denominators over a finite generating family of `D` so that the functional takes values in the
image of `R`. This is the bulk of `finiteDual_mem_associatedPrimes_of_comap_mem`, and carries
with it the whole tower `R → D → L` and `R → K → L` of local instances. -/
private theorem exists_nondegenerate_dual_of_finite_domain
    (R D : Type*) [CommRing R] [IsDomain R] [CommRing D] [IsDomain D] [Algebra R D]
    [Module.Finite R D] (hRD : Function.Injective (algebraMap R D)) :
    ∃ hD : D →ₗ[R] R, ∀ z : D, (∀ y : D, hD (z * y) = 0) → z = 0 := by
  classical
  let _ : FaithfulSMul R D := ⟨fun h => hRD (by
    simpa [Algebra.algebraMap_eq_smul_one] using h (1 : D))⟩
  let K := FractionRing R
  let L := FractionRing D
  let _ : Field K := FractionRing.field R
  let _ : Field L := FractionRing.field D
  let _ : SMul R L := (Module.compHom L (algebraMap R D)).toSMul
  let _ : Module R L := Module.compHom L (algebraMap R D)
  let _ : Algebra R L := Algebra.compHom L (algebraMap R D)
  let _ : IsScalarTower R D L :=
    IsScalarTower.of_algebraMap_eq' (Algebra.compHom_algebraMap_eq L (algebraMap R D))
  have hRL : Function.Injective (algebraMap R L) := by
    intro x y hxy
    rw [IsScalarTower.algebraMap_apply R D L] at hxy
    exact hRD ((IsFractionRing.injective D L) hxy)
  let _ : FaithfulSMul R L := ⟨fun h => hRL (by
    simpa [Algebra.algebraMap_eq_smul_one] using h (1 : L))⟩
  let _ : Algebra K L := FractionRing.liftAlgebra R L
  let _ : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  have hspan : Submodule.span K (Set.range (algebraMap D L)) = ⊤ := by
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := D)
    refine top_le_iff.mp ?_
    rw [← span_eq_top_localization_localization K (nonZeroDivisors R) (A := D) (Aₛ := L)
      (v := Set.range s) hs]
    apply Submodule.span_mono
    rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨s i, rfl⟩
  let φ : D →ₐ[R] L := {
    toRingHom := algebraMap D L
    commutes' := fun r => IsScalarTower.algebraMap_apply R D L r }
  let ell := fieldDualFunctional (K := K) (L := L)
  have hell : ell ≠ 0 := fieldDualFunctional_ne_zero
  have hfun := fieldFunctional_ann_eq_ker φ hspan ell hell
  let g : D →ₗ[R] K := ell.restrictScalars R |>.comp φ.toLinearMap
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := D)
  obtain ⟨d, hd, hden⟩ :=
    finite_denominators_clear (R := R) (K := K) n (fun i => g (s i))
  let dK : K := algebraMap R K d
  have hdK : dK ≠ 0 := fun h => hd (IsFractionRing.injective R K (by simpa [dK] using h))
  let g' : D →ₗ[R] K := g.smulRight dK
  let S : Submodule R K := LinearMap.range (Algebra.linearMap R K)
  have hgen : ∀ i, g' (s i) ∈ S := by
    intro i
    rcases hden i with ⟨r, hr⟩
    show ∃ r', algebraMap R K r' = g' (s i)
    refine ⟨r, ?_⟩
    simpa [g', LinearMap.smulRight_apply, dK, mul_comm] using hr
  have hall : ∀ z : D, g' z ∈ S := by
    intro z
    have hspan : ∀ y ∈ Submodule.span R (Set.range s), g' y ∈ S := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact hgen i
      | zero => simp
      | add y z hy hz ihy ihz => simpa using S.add_mem ihy ihz
      | smul r y hy ih => simpa using S.smul_mem r ih
    exact hspan z (by simp [hs])
  let hS : D →ₗ[R] S := LinearMap.codRestrict S g' hall
  have hcod : ∀ r : R, algebraMap R K r ∈ S := fun r => ⟨r, rfl⟩
  let e0 : R →ₗ[R] S := LinearMap.codRestrict S (Algebra.linearMap R K) hcod
  let e : R ≃ₗ[R] S := LinearEquiv.ofBijective e0 ⟨
    (fun a b hab => IsFractionRing.injective R K
      (congrArg (fun z : S => (z : K)) hab)),
    (fun z => by
      rcases z.2 with ⟨r, hr⟩
      exact ⟨r, Subtype.ext hr⟩)⟩
  let hD : D →ₗ[R] R := e.symm.toLinearMap.comp hS
  have hD_map (z : D) : algebraMap R K (hD z) = g' z := by
    calc
      algebraMap R K (hD z) = ((e (hD z) : S) : K) := rfl
      _ = (hS z : K) := congrArg (fun y : S => (y : K)) (e.apply_symm_apply (hS z))
      _ = g' z := rfl
  refine ⟨hD, fun z hz => ?_⟩
  have hz' : ∀ y : D, ell (φ (z * y)) = 0 := by
    intro y
    have hzero := congrArg (algebraMap R K) (hz y)
    rw [hD_map] at hzero
    have hmul : dK * ell (φ (z * y)) = 0 := by
      simpa [g', LinearMap.smulRight_apply, g, mul_comm] using hzero
    exact (mul_eq_zero.mp hmul).resolve_left hdK
  have hmem : z ∈ {c : D | ∀ x : D, ell (φ (c * x)) = 0} := hz'
  rw [hfun, SetLike.mem_coe, RingHom.mem_ker] at hmem
  exact IsFractionRing.injective D L (by simpa [φ] using hmem)

private theorem finiteDual_mem_associatedPrimes_of_comap_mem
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing C] [Module.Finite A C]
    (q : Ideal C) (hq : q.IsPrime)
    (hp : q.comap (algebraMap A C) ∈ associatedPrimes A A) :
    q ∈ associatedPrimes C (Module.Dual A C) := by
  let p := q.comap (algebraMap A C)
  let _ : p.IsPrime := hq.comap (algebraMap A C)
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp
  rcases hp with ⟨-, x, hx⟩
  let R := A ⧸ p
  let D := C ⧸ q
  let _ : Algebra R D := Ideal.Quotient.algebraQuotientOfLEComap le_rfl
  let _ : IsScalarTower A R D := .of_algebraMap_eq' rfl
  let _ : Module.Finite R D := Module.Finite.of_restrictScalars_finite A R D
  let _ : IsDomain R := Ideal.Quotient.isDomain p
  let _ : IsDomain D := Ideal.Quotient.isDomain q
  have hRD : Function.Injective (algebraMap R D) := Ideal.algebraMap_quotient_injective
  obtain ⟨hD, hannD⟩ := exists_nondegenerate_dual_of_finite_domain R D hRD
  let m : A →ₗ[A] A := LinearMap.mulLeft A x
  have hmker : m.ker = p := by
    ext a
    show m a = 0 ↔ a ∈ q.comap (algebraMap A C)
    rw [LinearMap.mulLeft_apply, hx]
    simp [Submodule.mem_colon_singleton, Submodule.mem_bot, mul_comm]
  let j : R →ₗ[A] A := p.liftQ m hmker.ge
  have hj : Function.Injective j :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' p m hmker.symm)
  let π : C →ₗ[A] D := (Ideal.Quotient.mkₐ A q).toLinearMap
  let f : Module.Dual A C := j.comp ((hD.restrictScalars A).comp π)
  have hcolon' : (⊥ : Submodule C (Module.Dual A C)).colon {f} = q := by
    ext c
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    show (c • f = 0) ↔ c ∈ q
    rw [LinearMap.ext_iff]
    show (∀ y : C, f (c * y) = 0) ↔ c ∈ q
    constructor
    · intro hc
      have hc' : ∀ z : D, hD ((Ideal.Quotient.mk q c) * z) = 0 := by
        intro z
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
        have hval : j (hD ((Ideal.Quotient.mk q c) * Ideal.Quotient.mk q y)) = j 0 := by
          simpa [f, π, map_mul] using hc y
        exact hj hval
      exact Ideal.Quotient.eq_zero_iff_mem.mp (hannD _ hc')
    · intro hc y
      simp [f, π, Ideal.Quotient.eq_zero_iff_mem.mpr hc]
  exact AssociatedPrimes.mem_iff.2 <| isAssociatedPrime_iff.2 ⟨hq, f, hcolon'.symm⟩

private theorem finiteDual_associatedPrimes_iff
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [IsNoetherianRing A] [IsNoetherianRing C] [Module.Finite A C]
    (q : Ideal C) (hq : q.IsPrime) :
    q ∈ associatedPrimes C (Module.Dual A C) ↔
      q.comap (algebraMap A C) ∈ associatedPrimes A A :=
  ⟨finiteDual_comap_associatedPrimes q, finiteDual_mem_associatedPrimes_of_comap_mem q hq⟩

private theorem associatedPrimes_comap_ringEquiv
    {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (e : R ≃+* S) (p : Ideal S) :
    letI : Module R M := Module.compHom M (e : R →+* S)
    p ∈ associatedPrimes S M ↔
      p.comap (e : R →+* S) ∈ associatedPrimes R M := by
  let _ : Module R M := Module.compHom M (e : R →+* S)
  constructor
  · intro hp
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp ⊢
    rcases hp with ⟨hp, x, hx⟩
    refine ⟨hp.comap e, x, ?_⟩
    rw [hx]
    ext r
    simp only [Ideal.mem_comap]
    show e r ∈ (⊥ : Submodule S M).colon {x} ↔
      r ∈ (⊥ : Submodule R M).colon {x}
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
    exact Iff.rfl
  · intro hp
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hp ⊢
    rcases hp with ⟨hpR, x, hxR⟩
    have hpS : p.IsPrime := by
      refine ⟨?_, ?_⟩
      · intro htop
        apply hpR.ne_top
        simp [htop]
      · intro a b hab
        have habR : e.symm a * e.symm b ∈ p.comap e := by
          show e (e.symm a * e.symm b) ∈ p
          simpa using hab
        rcases hpR.mem_or_mem habR with ha | hb
        · left
          change e (e.symm a) ∈ p at ha
          simpa using ha
        · right
          change e (e.symm b) ∈ p at hb
          simpa using hb
    refine ⟨hpS, x, ?_⟩
    ext s
    obtain ⟨r, hr⟩ := e.surjective s
    rw [← hr]
    show r ∈ p.comap e ↔ r ∈ (⊥ : Submodule R M).colon {x}
    rw [← hxR]
    rfl

/-- Associated primes of a localized module are those whose contraction is associated to the
module. -/
private theorem mem_associatedPrimes_localizedModule_iff
    {R : Type*} [CommRing R] [IsNoetherianRing R] (S : Submonoid R)
    (M : Type*) [AddCommGroup M] [Module R M] (q : Ideal (Localization S)) :
    q ∈ associatedPrimes (Localization S) (LocalizedModule S M) ↔
      q.comap (algebraMap R (Localization S)) ∈ associatedPrimes R M :=
  open Module.associatedPrimes in
  (Set.ext_iff.mp
    (preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
      (M := M) (R' := Localization S) S (f := LocalizedModule.mkLinearMap S M)) q).symm

private noncomputable def awayTensorEquiv
    {C B M : Type*} [CommRing C] [CommRing B] [Algebra C B]
    [AddCommGroup M] [Module C M] (g : C)
    (hbij : Function.Bijective (Localization.awayMap (algebraMap C B) g)) :
    let Cg := Localization.Away g;
    let Bg := Localization.Away (algebraMap C B g);
    let e : Cg ≃ₐ[C] Bg := AlgEquiv.ofBijective
      (Localization.awayMapₐ (IsScalarTower.toAlgHom C C B) g) hbij;
    let N := TensorProduct C M B;
    letI : Module B N := (TensorProduct.comm C M B).toAddEquiv.module B;
    letI : Module Cg (LocalizedModule (.powers g) M) := inferInstance;
    letI : Module Cg (LocalizedModule (.powers (algebraMap C B g)) N) :=
      Module.compHom _ e.toRingEquiv.toRingHom;
    LocalizedModule (.powers g) M ≃ₗ[Cg]
      LocalizedModule (.powers (algebraMap C B g)) N := by
  dsimp only
  let Cg := Localization.Away g
  let Bg := Localization.Away (algebraMap C B g)
  let e : Cg ≃ₐ[C] Bg := AlgEquiv.ofBijective
    (Localization.awayMapₐ (IsScalarTower.toAlgHom C C B) g) hbij
  let N := TensorProduct C M B
  let es := TensorProduct.comm C M B
  let _ : Module B N := es.toAddEquiv.module B
  let _ : Module B (B ⊗[C] M) := TensorProduct.leftModule
  let eSwap : N ≃ₗ[B] B ⊗[C] M :=
    es.toAddEquiv.toLinearEquiv (by
      intro b z
      change es.toAddEquiv (es.toAddEquiv.symm (b • es.toAddEquiv z)) = _
      exact es.toAddEquiv.apply_symm_apply _)
  let _ : Module Cg (LocalizedModule (.powers g) M) := inferInstance
  let _ : Module Bg (LocalizedModule (.powers (algebraMap C B g)) N) := inferInstance
  let _ : Module Cg (LocalizedModule (.powers (algebraMap C B g)) N) :=
    Module.compHom _ e.toRingEquiv.toRingHom
  let _ : Module Cg (Bg ⊗[C] M) := Module.compHom _ e.toRingEquiv.toRingHom
  let eSrc := LocalizedModule.equivTensorProduct (.powers g) M
  let eLoc := LocalizedModule.equivTensorProduct (.powers (algebraMap C B g)) N
  let swapMap0 := TensorProduct.map (LinearMap.id (R := B) (M := Bg)) eSwap.toLinearMap
  let swapMapInv0 := TensorProduct.map (LinearMap.id (R := B) (M := Bg)) eSwap.symm.toLinearMap
  let swapMap : Bg ⊗[B] N →ₗ[Bg] Bg ⊗[B] (B ⊗[C] M) := {
    toFun := swapMap0
    map_add' := swapMap0.map_add
    map_smul' := by
      intro a z
      induction z using TensorProduct.induction_on with
      | zero => simp [swapMap0]
      | tmul b n => simp [swapMap0, TensorProduct.smul_tmul']
      | add z w hz hw => simp [map_add, hz, hw] }
  let swapMapInv : Bg ⊗[B] (B ⊗[C] M) →ₗ[Bg] Bg ⊗[B] N := {
    toFun := swapMapInv0
    map_add' := swapMapInv0.map_add
    map_smul' := by
      intro a z
      induction z using TensorProduct.induction_on with
      | zero => simp [swapMapInv0]
      | tmul b n => simp [swapMapInv0, TensorProduct.smul_tmul']
      | add z w hz hw => simp [map_add, hz, hw] }
  let eSwapTensor : Bg ⊗[B] N ≃ₗ[Bg] Bg ⊗[B] (B ⊗[C] M) :=
    LinearEquiv.ofLinearMap swapMap swapMapInv (by
      ext b
      simp [swapMap, swapMapInv, swapMap0, swapMapInv0, TensorProduct.map_tmul]) (by
      ext b
      simp [swapMap, swapMapInv, swapMap0, swapMapInv0, TensorProduct.map_tmul])
  let eCancel := TensorProduct.AlgebraTensorModule.cancelBaseChange C B Bg Bg M
  let eTgt := eLoc.trans (eSwapTensor.trans eCancel)
  let map0 := TensorProduct.map e.toLinearMap (LinearMap.id (R := C) (M := M))
  let mapInv0 := TensorProduct.map e.symm.toLinearMap (LinearMap.id (R := C) (M := M))
  let mapF : Cg ⊗[C] M →ₗ[Cg] Bg ⊗[C] M := {
    toFun := map0
    map_add' := map0.map_add
    map_smul' := by
      intro a z
      induction z using TensorProduct.induction_on with
      | zero => simp [map0]
      | tmul x m =>
        change e (a * x) ⊗ₜ[C] m = a • (e x ⊗ₜ[C] m)
        rw [map_mul]
        change (e a * e x) ⊗ₜ[C] m = (e a * e x) ⊗ₜ[C] m
        rfl
      | add x y hx hy => simp [map_add, hx, hy] }
  let mapInv : Bg ⊗[C] M →ₗ[Cg] Cg ⊗[C] M := {
    toFun := mapInv0
    map_add' := mapInv0.map_add
    map_smul' := by
      intro a z
      induction z using TensorProduct.induction_on with
      | zero => simp [mapInv0]
      | tmul x m =>
        change e.symm (e a * x) ⊗ₜ[C] m = (a * e.symm x) ⊗ₜ[C] m
        rw [map_mul]
        simp
      | add x y hx hy => simp [map_add, hx, hy] }
  let eChange : Cg ⊗[C] M ≃ₗ[Cg] Bg ⊗[C] M :=
    LinearEquiv.ofLinearMap mapF mapInv (by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x m => simp [mapF, mapInv, map0, mapInv0, TensorProduct.map_tmul]
      | add x y hx hy => simp [map_add, hx, hy]) (by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x m => simp [mapF, mapInv, map0, mapInv0, TensorProduct.map_tmul]
      | add x y hx hy => simp [map_add, hx, hy])
  let eTgtCg : LocalizedModule (.powers (algebraMap C B g)) N ≃ₗ[Cg]
      Bg ⊗[C] M := {
    toFun := eTgt
    invFun := eTgt.symm
    left_inv := eTgt.symm_apply_apply
    right_inv := eTgt.apply_symm_apply
    map_add' := eTgt.map_add
    map_smul' := by
      intro a x
      change eTgt ((e a) • x) = (e a) • eTgt x
      exact eTgt.map_smul (e a) x }
  exact eSrc.trans (eChange.trans eTgtCg.symm)

open Module.associatedPrimes in
/-- **Stacks Project, Tag 0BVD.** A prime of an algebra with a finite-open factorization
is associated to its relative dualizing module if and only if it lies over an associated
prime of the base. -/
@[stacks 0BVD]
public theorem mem_associatedPrimes_dualizingModule_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (F : FiniteOpenFactorization.{u, v, w} A B) (q : PrimeSpectrum B) :
    q.asIdeal ∈ associatedPrimes B (dualizingModule F) ↔
      q.asIdeal.comap (algebraMap A B) ∈ associatedPrimes A A := by
  let C := F.middle
  let _ : CommRing C := F.commRingMiddle
  let _ : Algebra A C := F.algebraMiddle
  let _ : Algebra C B := F.algebraTarget
  let _ : IsScalarTower A C B := F.scalarTower
  let _ : Module.Finite A C := F.finite_middle
  let _ : IsNoetherianRing C := IsNoetherianRing.of_finite A C
  let p : Ideal C := q.asIdeal.comap (algebraMap C B)
  have hp : p.IsPrime := q.2.comap (algebraMap C B)
  let xC : PrimeSpectrum C := PrimeSpectrum.comap (algebraMap C B) q
  have hpOpen : xC ∈ Set.range (PrimeSpectrum.comap (algebraMap C B)) := ⟨q, rfl⟩
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hpg, hbasic⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hpOpen
      F.isOpenEmbedding_comap.isOpen_range
  have hg : g ∉ p := by simpa [xC, p] using hpg
  have hbij := F.awayMap_bijective g hbasic
  let Cg := Localization.Away g
  let Bg := Localization.Away (algebraMap C B g)
  let e : Cg ≃ₐ[C] Bg := AlgEquiv.ofBijective
    (Localization.awayMapₐ (IsScalarTower.toAlgHom C C B) g) hbij
  let pCg : Ideal Cg := p.map (algebraMap C Cg)
  have hpdisj : Disjoint (Submonoid.powers g : Set C) p :=
    Set.disjoint_left.mpr <| by
      rintro _ ⟨n, rfl⟩ hxP
      exact hg (hp.mem_of_pow_mem n hxP)
  have hpunder : pCg.comap (algebraMap C Cg) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers g) Cg hp hpdisj
  have hpCg : pCg.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) Cg p hp hpdisj
  let qBg : Ideal Bg := pCg.comap e.symm.toRingHom
  have hqBgPrime : qBg.IsPrime := hpCg.comap e.symm.toRingHom
  have hqBgE : qBg.comap e.toRingHom = pCg := by
    ext x
    simp [qBg]
  have hqBgOver : qBg.comap (algebraMap B Bg) = q.asIdeal := by
    let q' : Ideal B := qBg.comap (algebraMap B Bg)
    have hsquare :
        (algebraMap B Bg).comp (algebraMap C B) =
          e.toRingHom.comp (algebraMap C Cg) := by
      ext c
      exact (IsScalarTower.algebraMap_apply C B Bg c).symm.trans (e.commutes c).symm
    have hcontract : q'.comap (algebraMap C B) = p := by
      show qBg.comap ((algebraMap B Bg).comp (algebraMap C B)) = p
      rw [hsquare, Ideal.comap_comap]
      show (qBg.comap e.toRingHom).comap (algebraMap C Cg) = p
      rw [hqBgE, hpunder]
    have hq'prime : q'.IsPrime := hqBgPrime.comap (algebraMap B Bg)
    have hpoint :
        PrimeSpectrum.comap (algebraMap C B) ⟨q', hq'prime⟩ =
          PrimeSpectrum.comap (algebraMap C B) q :=
      PrimeSpectrum.ext hcontract
    exact congrArg PrimeSpectrum.asIdeal (F.isOpenEmbedding_comap.injective hpoint)
  let M := Module.Dual A C
  have hfinite := finiteDual_associatedPrimes_iff (A := A) (C := C) p hp
  let N := TensorProduct C M B
  let _ : Module B N := (TensorProduct.comm C M B).toAddEquiv.module B
  let awayEquiv := awayTensorEquiv (C := C) (B := B) (M := M) g hbij
  let _ : Module Cg
      (LocalizedModule (Submonoid.powers (algebraMap C B g)) N) :=
    Module.compHom _ e.toRingEquiv.toRingHom
  have hmodule :
      pCg ∈ associatedPrimes Cg (LocalizedModule (Submonoid.powers g) M) ↔
        pCg ∈ associatedPrimes Cg
          (LocalizedModule (Submonoid.powers (algebraMap C B g)) N) := by
    show IsAssociatedPrime pCg (LocalizedModule (Submonoid.powers g) M) ↔
      IsAssociatedPrime pCg
        (LocalizedModule (Submonoid.powers (algebraMap C B g)) N)
    exact awayEquiv.isAssociatedPrime_iff
  have hring := associatedPrimes_comap_ringEquiv
    (R := Cg) (S := Bg)
    (M := LocalizedModule (Submonoid.powers (algebraMap C B g)) N)
    e.toRingEquiv qBg
  have hlocalC := mem_associatedPrimes_localizedModule_iff (Submonoid.powers g) M pCg
  rw [hpunder] at hlocalC
  have hlocalB := mem_associatedPrimes_localizedModule_iff
    (Submonoid.powers (algebraMap C B g)) N qBg
  rw [hqBgOver] at hlocalB
  have hscalar :
      q.asIdeal ∈ associatedPrimes B N ↔
        p.comap (algebraMap A C) ∈ associatedPrimes A A := by
    calc
      q.asIdeal ∈ associatedPrimes B N ↔
          qBg ∈ associatedPrimes Bg
            (LocalizedModule (Submonoid.powers (algebraMap C B g)) N) :=
        hlocalB.symm
      _ ↔ pCg ∈ associatedPrimes Cg
            (LocalizedModule (Submonoid.powers (algebraMap C B g)) N) := by
        rw [← hqBgE]
        exact hring
      _ ↔ pCg ∈ associatedPrimes Cg
            (LocalizedModule (Submonoid.powers g) M) := hmodule.symm
      _ ↔ p ∈ associatedPrimes C M := hlocalC
      _ ↔ p.comap (algebraMap A C) ∈ associatedPrimes A A := hfinite
  have hpA : p.comap (algebraMap A C) = q.asIdeal.comap (algebraMap A B) := by
    ext a
    show algebraMap C B (algebraMap A C a) ∈ q.asIdeal ↔
      algebraMap A B a ∈ q.asIdeal
    rw [← IsScalarTower.algebraMap_apply A C B a]
  let eN : N ≃ₗ[B] dualizingModule F := LinearEquiv.refl B N
  have hN : q.asIdeal ∈ associatedPrimes B N ↔
      q.asIdeal ∈ associatedPrimes B (dualizingModule F) := by
    show IsAssociatedPrime q.asIdeal N ↔
      IsAssociatedPrime q.asIdeal (dualizingModule F)
    exact eN.isAssociatedPrime_iff
  exact hN.symm.trans (by simpa [hpA] using hscalar)

end Stacks.Discriminant
