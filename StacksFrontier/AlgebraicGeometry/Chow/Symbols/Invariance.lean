module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Multiplicativity
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Unit
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.RingTheory.KrullDimension.Module
public import StacksFrontier.RingTheory.Support.Finite
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.SupportLength

/-!
# Invariance of the module symbol under a zero-dimensional modification

A homomorphism between finite modules of dimension one preserves the symbol when its kernel and
cokernel have support of dimension at most zero.

## Main results

* `AlgebraicGeometry.moduleSymbol_eq_of_ker_coker_supportDim_le_zero` compares the symbols of
  the source and target modules.

## Implementation notes

The cokernel is represented by the quotient of the target by the range of the homomorphism.
The dimensions of the kernel and cokernel are expressed using `Module.supportDim`. The proof
reduces first to a map whose cokernel is annihilated by both elements, then to a simple
cokernel, then by induction on the length of the cokernel.

## References

* [Stacks Project, Tag 02Q4](https://stacks.math.columbia.edu/tag/02Q4)
-/

@[expose] public section

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v w

/-- The symbol is multiplicative in its first argument. -/
private theorem moduleSymbol_mul_left
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b c : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hc : IsSMulRegular M c) (hdim : Module.supportDim A M = 1) :
    moduleSymbol (a * b) c (ha.mul hb) hc hdim =
      moduleSymbol a c ha hc hdim * moduleSymbol b c hb hc hdim := by
  let s (x y : A) (hx : IsSMulRegular M x) (hy : IsSMulRegular M y) :=
    moduleSymbol x y hx hy hdim
  show s (a * b) c (ha.mul hb) hc = s a c ha hc * s b c hb hc
  have h₁' : s (a * b) c (ha.mul hb) hc * s c (a * b) hc (ha.mul hb) = 1 :=
    moduleSymbol_mul_swap (A := A) (M := M) (a := a * b) c (ha.mul hb) hc hdim
  have h₂' : s c a hc ha * s c b hc hb = s c (a * b) hc (ha.mul hb) :=
    (moduleSymbol_mul_right (A := A) (M := M) c a b hc ha hb hdim).symm
  have h₃' : s a c ha hc * s c a hc ha = 1 :=
    moduleSymbol_mul_swap (A := A) (M := M) a c ha hc hdim
  have h₄' : s b c hb hc * s c b hc hb = 1 :=
    moduleSymbol_mul_swap (A := A) (M := M) b c hb hc hdim
  calc
    s (a * b) c (ha.mul hb) hc = (s c (a * b) hc (ha.mul hb))⁻¹ :=
      eq_inv_of_mul_eq_one_left h₁'
    _ = (s c a hc ha * s c b hc hb)⁻¹ := by rw [h₂']
    _ = (s c a hc ha)⁻¹ * (s c b hc hb)⁻¹ := by simp [mul_comm]
    _ = s a c ha hc * s b c hb hc := by
      rw [← eq_inv_of_mul_eq_one_left h₃', ← eq_inv_of_mul_eq_one_left h₄']

/-- A map whose kernel has support of dimension at most zero is injective, given an element of
the maximal ideal acting regularly on the source. -/
private theorem injective_of_ker_supportDim_le_zero
    {A : Type*} {M : Type*} {M' : Type*} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup M'] [Module A M']
    (f : M →ₗ[A] M') (a : A) (ha : IsSMulRegular M a)
    (haM : a ∈ IsLocalRing.maximalIdeal A)
    (hker : Module.supportDim A (LinearMap.ker f) ≤ 0) : Function.Injective f := by
  classical
  by_contra hnot
  have hkerbot : LinearMap.ker f ≠ ⊥ := fun h => hnot (LinearMap.ker_eq_bot.mp h)
  have : Nontrivial (LinearMap.ker f) := Submodule.nontrivial_iff_ne_bot.mpr hkerbot
  have hdim : Module.supportDim A (LinearMap.ker f) = 0 := by
    apply le_antisymm hker
    cases hd : Module.supportDim A (LinearMap.ker f) with
    | bot => exact (Module.supportDim_ne_bot_of_nontrivial A (LinearMap.ker f) hd).elim
    | coe n => exact WithBot.coe_le_coe.mpr bot_le
  have hsupp : Module.support A (LinearMap.ker f) = {IsLocalRing.closedPoint A} := by
    ext q
    rw [support_of_supportDim_eq_zero A _ hdim]
    simp only [PrimeSpectrum.mem_zeroLocus, Set.mem_singleton_iff]
    exact ⟨fun h => PrimeSpectrum.ext
      (le_antisymm (IsLocalRing.le_maximalIdeal q.isPrime.ne_top) h), by rintro rfl; exact le_rfl⟩
  have hmin : Minimal (· ∈ Module.support A (LinearMap.ker f))
      (IsLocalRing.closedPoint A) := by
    rw [hsupp]
    show IsLocalRing.closedPoint A ∈
        ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) ∧
      ∀ ⦃q : PrimeSpectrum A⦄, q ∈ {IsLocalRing.closedPoint A} →
        q ≤ IsLocalRing.closedPoint A → IsLocalRing.closedPoint A ≤ q
    exact ⟨Set.mem_singleton _, fun q hq _ => (Set.mem_singleton_iff.mp hq).ge⟩
  have hk : IsLocalRing.maximalIdeal A ∈ associatedPrimes A (LinearMap.ker f) :=
    Module.mem_associatedPrimes_of_minimal_mem_support hmin
  have hm : IsLocalRing.maximalIdeal A ∈ associatedPrimes A M :=
    AssociatedPrimes.mem_iff.mpr
      ((AssociatedPrimes.mem_iff.mp hk).map_of_injective (LinearMap.ker f).subtype
        (LinearMap.ker f).injective_subtype)
  have hmem : a ∈ ⋃ p ∈ associatedPrimes A M, (p : Set A) := Set.mem_biUnion hm haM
  rw [biUnion_associatedPrimes_eq_compl_regular A M] at hmem
  exact hmem ha

/-- The maximal ideal of a local ring annihilates a simple module. -/
private theorem smul_eq_zero_of_simple_module
    {A C : Type*} [CommRing A] [IsLocalRing A]
    [AddCommGroup C] [Module A C] (hC : IsSimpleModule A C)
    (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A) : ∀ x : C, a • x = 0 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hC
  have haI : a ∈ I := IsLocalRing.eq_maximalIdeal hI ▸ ha
  intro x
  apply e.injective
  rw [map_smul, map_zero]
  obtain ⟨d, hd⟩ := Submodule.mkQ_surjective I (e x)
  rw [← hd]
  calc
    a • (Submodule.Quotient.mk d : A ⧸ I) = Submodule.Quotient.mk (a • d) :=
      (Submodule.Quotient.mk_smul I a d).symm
    _ = 0 := (Submodule.Quotient.mk_eq_zero I).mpr (by
      simpa [smul_eq_mul] using I.mul_mem_right d haI)

/-- An injection whose cokernel is annihilated by both elements preserves the symbol. -/
private theorem moduleSymbol_eq_of_injective_coker_annihilated
    {A : Type u} {M : Type v} {M' : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup M'] [Module A M'] [Module.Finite A M']
    (α : M →ₗ[A] M') (a b : A)
    (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (ha' : IsSMulRegular M' a) (hb' : IsSMulRegular M' b)
    (hdim : Module.supportDim A M = 1) (hdim' : Module.supportDim A M' = 1)
    (hα : Function.Injective α)
    (hCa : ∀ x : M' ⧸ LinearMap.range α, a • x = 0)
    (hCb : ∀ x : M' ⧸ LinearMap.range α, b • x = 0) :
    moduleSymbol a b ha hb hdim = moduleSymbol a b ha' hb' hdim' := by
  let φ : M →ₗ[A] M := LinearMap.lsmul A M a
  let ψ : M →ₗ[A] M := LinearMap.lsmul A M b
  let φ' : M' →ₗ[A] M' := LinearMap.lsmul A M' a
  let ψ' : M' →ₗ[A] M' := LinearMap.lsmul A M' b
  let hcomm := range_lsmul_comp_comm (M := M) a b
  let hcomm' := range_lsmul_comp_comm (M := M') a b
  let X := M ⧸ LinearMap.range (φ ∘ₗ ψ)
  let Y := M' ⧸ LinearMap.range (φ' ∘ₗ ψ')
  let f := periodicQuotientPhi φ ψ hcomm
  let g := periodicQuotientPsi φ ψ hcomm
  let f' := periodicQuotientPhi φ' ψ' hcomm'
  let g' := periodicQuotientPsi φ' ψ' hcomm'
  have hmap : LinearMap.range (φ ∘ₗ ψ) ≤
      Submodule.comap α (LinearMap.range (φ' ∘ₗ ψ')) := by
    rintro _ ⟨x, rfl⟩
    refine ⟨α x, ?_⟩
    simp [φ, ψ, φ', ψ', LinearMap.comp_apply, LinearMap.lsmul_apply, map_smul]
  let β : X →ₗ[A] Y :=
    Submodule.mapQ (LinearMap.range (φ ∘ₗ ψ)) (LinearMap.range (φ' ∘ₗ ψ')) α hmap
  have hφ : Function.Exact f g := exact_mul_left_right a b hb
  have hψ : Function.Exact g f := exact_mul_right_left a b ha
  have hφ' : Function.Exact f' g' := exact_mul_left_right a b hb'
  have hψ' : Function.Exact g' f' := exact_mul_right_left a b ha'
  have hβf : β.comp f = f'.comp β := by
    ext x
    show (LinearMap.range (φ' ∘ₗ ψ')).mkQ (α (φ x)) =
      (LinearMap.range (φ' ∘ₗ ψ')).mkQ (φ' (α x))
    simp [φ, φ', LinearMap.lsmul_apply, map_smul]
  have hβg : β.comp g = g'.comp β := by
    ext x
    show (LinearMap.range (φ' ∘ₗ ψ')).mkQ (α (ψ x)) =
      (LinearMap.range (φ' ∘ₗ ψ')).mkQ (ψ' (α x))
    simp [ψ, ψ', LinearMap.lsmul_apply, map_smul]
  have lift (c : A) (hC : ∀ x : M' ⧸ LinearMap.range α, c • x = 0) (x : M') :
      ∃ y : M, α y = c • x := by
    have hx : (LinearMap.range α).mkQ (c • x) = 0 := by
      simpa [Submodule.mkQ_apply, map_smul] using hC ((LinearMap.range α).mkQ x)
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range α)).mp hx
  have hker_f : LinearMap.ker β ≤ LinearMap.ker f := by
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (φ ∘ₗ ψ)) z
    change (LinearMap.range (φ' ∘ₗ ψ')).mkQ (α x) = 0 at hz
    have hz' : α x ∈ LinearMap.range (φ' ∘ₗ ψ') :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨y, hy⟩ := hz'
    obtain ⟨z, hz⟩ := lift a hCa y
    have hxy : α x = a • (b • y) := by
      simpa only [φ', ψ', LinearMap.comp_apply, LinearMap.lsmul_apply] using hy.symm
    have hx : x = b • z := hα (by
      calc
        α x = a • (b • y) := hxy
        _ = α (b • z) := by rw [map_smul, hz, smul_comm])
    show (LinearMap.range (φ ∘ₗ ψ)).mkQ (a • x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    subst x
    refine ⟨z, ?_⟩
    simp only [φ, ψ, LinearMap.comp_apply, LinearMap.lsmul_apply, smul_smul]
  have hker_g : LinearMap.ker β ≤ LinearMap.ker g := by
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (φ ∘ₗ ψ)) z
    change (LinearMap.range (φ' ∘ₗ ψ')).mkQ (α x) = 0 at hz
    have hz' : α x ∈ LinearMap.range (φ' ∘ₗ ψ') :=
      (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨y, hy⟩ := hz'
    obtain ⟨z, hz⟩ := lift b hCb y
    have hxy : α x = a • (b • y) := by
      simpa only [φ', ψ', LinearMap.comp_apply, LinearMap.lsmul_apply] using hy.symm
    have hx : x = a • z := hα (by
      calc
        α x = a • (b • y) := hxy
        _ = α (a • z) := by rw [map_smul, hz, smul_smul])
    show (LinearMap.range (φ ∘ₗ ψ)).mkQ (b • x) = 0
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    subst x
    refine ⟨z, ?_⟩
    simp only [φ, ψ, LinearMap.comp_apply, LinearMap.lsmul_apply, smul_smul]
    exact congrArg (fun r : A => r • z) (mul_comm a b)
  have hQf : LinearMap.range f' ≤ LinearMap.range β := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (φ' ∘ₗ ψ')) q
    obtain ⟨y, hy⟩ := lift a hCa x
    refine ⟨(LinearMap.range (φ ∘ₗ ψ)).mkQ y, ?_⟩
    show β ((LinearMap.range (φ ∘ₗ ψ)).mkQ y) =
      f' ((LinearMap.range (φ' ∘ₗ ψ')).mkQ x)
    show (LinearMap.range (φ' ∘ₗ ψ')).mkQ (α y) = _
    show (LinearMap.range (φ' ∘ₗ ψ')).mkQ (α y) =
      (LinearMap.range (φ' ∘ₗ ψ')).mkQ (φ' x)
    rw [hy]
    rfl
  have hQg : LinearMap.range g' ≤ LinearMap.range β := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (φ' ∘ₗ ψ')) q
    obtain ⟨y, hy⟩ := lift b hCb x
    refine ⟨(LinearMap.range (φ ∘ₗ ψ)).mkQ y, ?_⟩
    show β ((LinearMap.range (φ ∘ₗ ψ)).mkQ y) =
      g' ((LinearMap.range (φ' ∘ₗ ψ')).mkQ x)
    show (LinearMap.range (φ' ∘ₗ ψ')).mkQ (α y) = _
    show (LinearMap.range (φ' ∘ₗ ψ')).mkQ (α y) =
      (LinearMap.range (φ' ∘ₗ ψ')).mkQ (ψ' x)
    rw [hy]
    rfl
  let c := connectingEquivs f g f' g' β hφ hψ hφ' hψ' hβf hβg hker_f hker_g hQf hQg
  have hconn : c.1.1 = c.1.2 := by
    apply LinearEquiv.ext
    intro q
    obtain ⟨q, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range β) q
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (φ' ∘ₗ ψ')) q
    obtain ⟨y, hy⟩ := lift a hCa x
    obtain ⟨z, hz⟩ := lift b hCb x
    have hzy : b • y = a • z := hα (by
      calc
        α (b • y) = b • (a • x) := by rw [map_smul, hy]
        _ = a • (b • x) := by rw [smul_comm]
        _ = α (a • z) := by rw [map_smul, hz])
    have hy' : β ((LinearMap.range (φ ∘ₗ ψ)).mkQ y) =
        f' ((LinearMap.range (φ' ∘ₗ ψ')).mkQ x) := by
      show (LinearMap.range (φ' ∘ₗ ψ')).mkQ (α y) = _
      rw [hy]
      simp [f', periodicQuotientPhi, φ', ψ', LinearMap.lsmul_apply]
    have hz' : β ((LinearMap.range (φ ∘ₗ ψ)).mkQ z) =
        g' ((LinearMap.range (φ' ∘ₗ ψ')).mkQ x) := by
      show (LinearMap.range (φ' ∘ₗ ψ')).mkQ (α z) = _
      rw [hz]
      simp [g', periodicQuotientPsi, φ', ψ', LinearMap.lsmul_apply]
    apply Subtype.ext
    have he1 := c.2.1 ((LinearMap.range (φ' ∘ₗ ψ')).mkQ x)
      ((LinearMap.range (φ ∘ₗ ψ)).mkQ y) hy'
    have he2 := c.2.2 ((LinearMap.range (φ' ∘ₗ ψ')).mkQ x)
      ((LinearMap.range (φ ∘ₗ ψ)).mkQ z) hz'
    have he1' : ↑(c.1.1 ((LinearMap.range β).mkQ
        ((LinearMap.range (φ' ∘ₗ ψ')).mkQ x))) =
        g ((LinearMap.range (φ ∘ₗ ψ)).mkQ y) := by simpa using he1
    have he2' : ↑(c.1.2 ((LinearMap.range β).mkQ
        ((LinearMap.range (φ' ∘ₗ ψ')).mkQ x))) =
        f ((LinearMap.range (φ ∘ₗ ψ)).mkQ z) := by simpa using he2
    rw [he1', he2']
    show (LinearMap.range (φ ∘ₗ ψ)).mkQ (b • y) =
      (LinearMap.range (φ ∘ₗ ψ)).mkQ (a • z)
    exact congrArg _ hzy
  have hdet := periodicDeterminant_eq_of_connecting_eq
    f g f' g' β
    (isFiniteLength_quotient_mul a b ha hb hdim)
    (isFiniteLength_quotient_mul a b ha' hb' hdim')
    hφ hψ hφ' hψ' hβf hβg hker_f hker_g hQf hQg hconn
  show periodicDeterminant f g hφ hψ
      (isFiniteLength_quotient_mul a b ha hb hdim) =
    periodicDeterminant f' g' hφ' hψ'
      (isFiniteLength_quotient_mul a b ha' hb' hdim')
  exact hdet

/-- An injection with simple cokernel preserves the symbol, for elements of the maximal ideal. -/
private theorem moduleSymbol_eq_of_injective_simple_coker
    {A : Type u} {M : Type v} {M' : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup M'] [Module A M'] [Module.Finite A M']
    (α : M →ₗ[A] M') (a b : A)
    (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (ha' : IsSMulRegular M' a) (hb' : IsSMulRegular M' b)
    (hdim : Module.supportDim A M = 1) (hdim' : Module.supportDim A M' = 1)
    (hα : Function.Injective α)
    (hC : IsSimpleModule A (M' ⧸ LinearMap.range α))
    (haM : a ∈ IsLocalRing.maximalIdeal A) (hbM : b ∈ IsLocalRing.maximalIdeal A) :
    moduleSymbol a b ha hb hdim = moduleSymbol a b ha' hb' hdim' := by
  apply moduleSymbol_eq_of_injective_coker_annihilated α a b ha hb ha' hb' hdim hdim' hα
  · exact smul_eq_zero_of_simple_module hC a haM
  · exact smul_eq_zero_of_simple_module hC b hbM

/-- An injection with finite-length cokernel preserves the symbol, for elements of the maximal
ideal. -/
private theorem moduleSymbol_eq_of_injective_finite_coker_equiv
    {A : Type u} {C : Type*} {M : Type v} {M' : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup C] [Module A C]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup M'] [Module A M'] [Module.Finite A M']
    (hc : IsFiniteLength A C) (α : M →ₗ[A] M')
    (e : (M' ⧸ LinearMap.range α) ≃ₗ[A] C)
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (ha' : IsSMulRegular M' a) (hb' : IsSMulRegular M' b)
    (hdim : Module.supportDim A M = 1) (hdim' : Module.supportDim A M' = 1)
    (hα : Function.Injective α)
    (haM : a ∈ IsLocalRing.maximalIdeal A) (hbM : b ∈ IsLocalRing.maximalIdeal A) :
    moduleSymbol a b ha hb hdim = moduleSymbol a b ha' hb' hdim' := by
  classical
  induction hc generalizing M M' α ha hb ha' hb' hdim hdim' hα with
  | @of_subsingleton C instAdd instModule instSub =>
      let : Subsingleton C := instSub
      let : Subsingleton (M' ⧸ LinearMap.range α) :=
        ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
      apply moduleSymbol_eq_of_injective_coker_annihilated α a b ha hb ha' hb'
        hdim hdim' hα
      · intro x
        exact Subsingleton.elim _ _
      · intro x
        exact Subsingleton.elim _ _
  | @of_simple_quotient C _ _ N _ hN ih =>
      let q₀ : M' →ₗ[A] C := e.toLinearMap.comp (LinearMap.range α).mkQ
      let U : Submodule A M' := N.comap q₀
      have hαU_mem : ∀ x : M, α x ∈ U := by
        intro x
        show e ((LinearMap.range α).mkQ (α x)) ∈ N
        have hx : (LinearMap.range α).mkQ (α x) = 0 :=
          (Submodule.Quotient.mk_eq_zero (LinearMap.range α)).2 ⟨x, rfl⟩
        rw [hx]
        simp
      let αU : M →ₗ[A] U := LinearMap.codRestrict U α hαU_mem
      have hαU : Function.Injective αU := by
        intro x y hxy
        apply hα
        exact congrArg Subtype.val hxy
      let qU : U →ₗ[A] N := LinearMap.codRestrict N (q₀.comp U.subtype)
        (fun x => x.property)
      have hqU_surj : Function.Surjective qU := by
        intro n
        obtain ⟨x, hx⟩ := e.surjective n
        obtain ⟨y, hy⟩ := (LinearMap.range α).mkQ_surjective x
        have hq0y : q₀ y = n.val := by
          show e ((LinearMap.range α).mkQ y) = n.val
          rw [hy, hx]
        refine ⟨⟨y, ?_⟩, ?_⟩
        · show q₀ y ∈ N
          rw [hq0y]
          exact n.property
        · apply Subtype.ext
          exact hq0y
      have hker_qU : LinearMap.ker qU = LinearMap.range αU := by
        ext x
        constructor
        · intro hx
          have hx0 : q₀ x.val = 0 := by
            have h := congrArg Subtype.val hx
            change q₀ x.val = 0 at h
            exact h
          have hquot : (LinearMap.range α).mkQ x.val = 0 := e.injective (by
            simpa [q₀] using hx0)
          have hxrange : x.val ∈ LinearMap.range α :=
            (Submodule.Quotient.mk_eq_zero _).mp hquot
          obtain ⟨y, hy⟩ := hxrange
          refine ⟨y, ?_⟩
          apply Subtype.ext
          exact hy
        · rintro ⟨y, rfl⟩
          apply LinearMap.mem_ker.mpr
          apply Subtype.ext
          show e ((LinearMap.range α).mkQ (α y)) = 0
          rw [Submodule.mkQ_apply,
            (Submodule.Quotient.mk_eq_zero (LinearMap.range α)).2 ⟨y, rfl⟩]
          simp
      let eU : (U ⧸ LinearMap.range αU) ≃ₗ[A] N :=
        (Submodule.quotEquivOfEq _ _ hker_qU.symm).trans
            ((LinearMap.quotKerEquivRange qU).trans
            ((LinearEquiv.ofEq _ _ (LinearMap.range_eq_top.mpr hqU_surj)).trans
              Submodule.topEquiv))
      have hregU (c : A) (hc : IsSMulRegular M' c) : IsSMulRegular U c := by
        intro x y hxy
        apply Subtype.ext
        exact hc (by simpa using congrArg Subtype.val hxy)
      have haU := hregU a ha'
      have hbU := hregU b hb'
      have hdimU : Module.supportDim A U = 1 := by
        apply le_antisymm
        · calc
            Module.supportDim A U ≤ Module.supportDim A M' :=
              Module.supportDim_le_of_injective U.subtype U.injective_subtype
            _ = 1 := hdim'
        · calc
            1 = Module.supportDim A M := hdim.symm
            _ ≤ Module.supportDim A U := Module.supportDim_le_of_injective αU hαU
      have hIH := ih αU eU ha hb haU hbU hdim hdimU hαU
      let β : U →ₗ[A] M' := U.subtype
      let δ : M' →ₗ[A] C ⧸ N := N.mkQ.comp q₀
      have hδ_surj : Function.Surjective δ := N.mkQ_surjective.comp
        (e.surjective.comp (LinearMap.range α).mkQ_surjective)
      have hker_δ : LinearMap.ker δ = LinearMap.range β := by
        ext x
        show δ x = 0 ↔ x ∈ LinearMap.range β
        show N.mkQ (q₀ x) = 0 ↔ x ∈ LinearMap.range β
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        show q₀ x ∈ N ↔ ∃ y : U, (β y : M') = x
        constructor
        · intro hx
          exact ⟨⟨x, hx⟩, rfl⟩
        · rintro ⟨y, rfl⟩
          exact y.property
      let eβ : (M' ⧸ LinearMap.range β) ≃ₗ[A] C ⧸ N :=
        (Submodule.quotEquivOfEq _ _ hker_δ.symm).trans
            ((LinearMap.quotKerEquivRange δ).trans
            ((LinearEquiv.ofEq _ _ (LinearMap.range_eq_top.mpr hδ_surj)).trans
              Submodule.topEquiv))
      have hSimpleβ : IsSimpleModule A (M' ⧸ LinearMap.range β) :=
        IsSimpleModule.congr eβ
      have hβ : Function.Injective β := U.injective_subtype
      have hβcmp := moduleSymbol_eq_of_injective_simple_coker β a b haU hbU ha' hb'
        hdimU hdim' hβ hSimpleβ haM hbM
      exact hIH.trans hβcmp

/-- Invariance of the symbol when both elements lie in the maximal ideal. -/
private theorem moduleSymbol_eq_of_both_in_maximalIdeal
    {A : Type u} {M : Type v} {M' : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup M'] [Module A M'] [Module.Finite A M']
    (α : M →ₗ[A] M') (a b : A)
    (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (ha' : IsSMulRegular M' a) (hb' : IsSMulRegular M' b)
    (hdim : Module.supportDim A M = 1) (hdim' : Module.supportDim A M' = 1)
    (hker : Module.supportDim A (LinearMap.ker α) ≤ 0)
    (hcoker : Module.supportDim A (M' ⧸ LinearMap.range α) ≤ 0)
    (haM : a ∈ IsLocalRing.maximalIdeal A)
    (hbM : b ∈ IsLocalRing.maximalIdeal A) :
    moduleSymbol a b ha hb hdim = moduleSymbol a b ha' hb' hdim' := by
  have hα := injective_of_ker_supportDim_le_zero α a ha haM hker
  have hC := finite_length_of_supportDim_le_zero hcoker
  exact moduleSymbol_eq_of_injective_finite_coker_equiv hC α
    (LinearEquiv.refl A (M' ⧸ LinearMap.range α)) a b ha hb ha' hb'
    hdim hdim' hα haM hbM

/-- The symbol of two units is trivial. -/
private theorem moduleSymbol_unit_unit
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (u v : Aˣ) (hdim : Module.supportDim A M = 1) :
    moduleSymbol (u : A) (v : A) (Units.isSMulRegular M u) (Units.isSMulRegular M v) hdim = 1 := by
  have hr : LinearMap.range (LinearMap.lsmul A M (v : A)) = ⊤ :=
    LinearMap.range_eq_top.mpr fun x => ⟨(↑(v⁻¹) : A) • x, by simp [smul_smul]⟩
  have hs := moduleSymbol_unit_left u (v : A) (Units.isSMulRegular M v) hdim
  rw [hr] at hs
  apply Units.ext
  simpa [moduleLength, Module.length_eq_zero] using hs

/-- **Stacks Project, Tag 02Q4.** The symbol is unchanged by a map of one-dimensional finite
modules whose kernel and cokernel have support dimension at most zero. -/
@[stacks 02Q4]
theorem moduleSymbol_eq_of_ker_coker_supportDim_le_zero
    {A : Type u} {M : Type v} {M' : Type w}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup M'] [Module A M'] [Module.Finite A M']
    (α : M →ₗ[A] M') (a b : A)
    (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (ha' : IsSMulRegular M' a) (hb' : IsSMulRegular M' b)
    (hdim : Module.supportDim A M = 1)
    (hdim' : Module.supportDim A M' = 1)
    (hker : Module.supportDim A (LinearMap.ker α) ≤ 0)
    (hcoker : Module.supportDim A (M' ⧸ LinearMap.range α) ≤ 0) :
    moduleSymbol a b ha hb hdim = moduleSymbol a b ha' hb' hdim' := by
  classical
  by_cases haUnit : IsUnit a
  · by_cases hbUnit : IsUnit b
    · obtain ⟨u, rfl⟩ := haUnit
      obtain ⟨v, rfl⟩ := hbUnit
      exact (moduleSymbol_unit_unit u v hdim).trans (moduleSymbol_unit_unit u v hdim').symm
    · have hbM : b ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 hbUnit
      have hmulM := moduleSymbol_mul_left a b b ha hb hb hdim
      have hmulM' := moduleSymbol_mul_left a b b ha' hb' hb' hdim'
      have h₁ := moduleSymbol_eq_of_both_in_maximalIdeal α (a * b) b (ha.mul hb) hb
        (ha'.mul hb') hb' hdim hdim' hker hcoker
        (by simpa [mul_comm] using (IsLocalRing.maximalIdeal A).mul_mem_right a hbM) hbM
      have h₂ := moduleSymbol_eq_of_both_in_maximalIdeal α b b hb hb hb' hb'
        hdim hdim' hker hcoker hbM hbM
      calc
        moduleSymbol a b ha hb hdim =
            (moduleSymbol a b ha hb hdim * moduleSymbol b b hb hb hdim) *
                (moduleSymbol b b hb hb hdim)⁻¹ := by simp
        _ = moduleSymbol (a * b) b (ha.mul hb) hb hdim *
              (moduleSymbol b b hb hb hdim)⁻¹ := by rw [hmulM]
        _ = moduleSymbol (a * b) b (ha'.mul hb') hb' hdim' *
              (moduleSymbol b b hb' hb' hdim')⁻¹ := by rw [h₁, h₂]
        _ = moduleSymbol a b ha' hb' hdim' := by rw [hmulM']; simp
  · by_cases hbUnit : IsUnit b
    · have haM : a ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 haUnit
      have hmulM := moduleSymbol_mul_right a b a ha hb ha hdim
      have hmulM' := moduleSymbol_mul_right a b a ha' hb' ha' hdim'
      have h₁ := moduleSymbol_eq_of_both_in_maximalIdeal α a (b * a) ha (hb.mul ha)
        ha' (hb'.mul ha') hdim hdim' hker hcoker
        haM (by simpa [mul_comm] using (IsLocalRing.maximalIdeal A).mul_mem_right b haM)
      have h₂ := moduleSymbol_eq_of_both_in_maximalIdeal α a a ha ha ha' ha'
        hdim hdim' hker hcoker haM haM
      calc
        moduleSymbol a b ha hb hdim =
            (moduleSymbol a b ha hb hdim * moduleSymbol a a ha ha hdim) *
                (moduleSymbol a a ha ha hdim)⁻¹ := by simp
        _ = moduleSymbol a (b * a) ha (hb.mul ha) hdim *
              (moduleSymbol a a ha ha hdim)⁻¹ := by rw [hmulM]
        _ = moduleSymbol a (b * a) ha' (hb'.mul ha') hdim' *
              (moduleSymbol a a ha' ha' hdim')⁻¹ := by rw [h₁, h₂]
        _ = moduleSymbol a b ha' hb' hdim' := by rw [hmulM']; simp
    · have haM : a ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 haUnit
      have hbM : b ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 hbUnit
      exact moduleSymbol_eq_of_both_in_maximalIdeal α a b ha hb ha' hb'
        hdim hdim' hker hcoker haM hbM

end AlgebraicGeometry
