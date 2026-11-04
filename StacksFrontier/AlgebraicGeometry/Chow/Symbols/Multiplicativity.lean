module

public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Multiplicativity
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Swap
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Basic

/-!
# Multiplicativity of the symbol of a finite module

For a finite module of support dimension one over a Noetherian local ring, the symbol is
multiplicative in its second argument. The symbols obtained by interchanging the two arguments
are inverse to each other.

## Main results

* `AlgebraicGeometry.moduleSymbol_mul_right` gives multiplicativity in the second argument.
* `AlgebraicGeometry.moduleSymbol_mul_swap` gives the inverse relation on swapping arguments.

## Implementation notes

Regularity of a product is obtained from regularity of its two factors.

## References

* [Stacks Project, Tag 02Q0](https://stacks.math.columbia.edu/tag/02Q0)
-/

@[expose] public section

namespace AlgebraicGeometry

universe u v

/-- Exactness transfers along an isomorphism of periodic complexes. -/
private theorem exact_of_linearEquiv
    {R : Type u} {M : Type v} {M' : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid M'] [Module R M']
    (e : M ≃ₗ[R] M') (φ ψ : M →ₗ[R] M)
    (φ' ψ' : M' →ₗ[R] M')
    (hφ : e.toLinearMap.comp φ = φ'.comp e.toLinearMap)
    (hψ : e.toLinearMap.comp ψ = ψ'.comp e.toLinearMap)
    (hExact : Function.Exact φ ψ) : Function.Exact φ' ψ' := by
  exact Function.Exact.of_ladder_linearEquiv_of_exact (e₁ := e) (e₂ := e) (e₃ := e)
    hφ.symm hψ.symm hExact

/-- **Stacks Project, Tag 02Q0.** The symbol is multiplicative in its second argument. -/
@[stacks 02Q0 "multiplicativity"]
theorem moduleSymbol_mul_right
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b c : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hc : IsSMulRegular M c) (hdim : Module.supportDim A M = 1) :
    moduleSymbol a (b * c) ha (hb.mul hc) hdim =
      moduleSymbol a b ha hb hdim * moduleSymbol a c ha hc hdim := by
  let hcommA := range_lsmul_comp_comm (M := M) a (b * c)
  let hcommB := range_lsmul_comp_comm (M := M) b (a * c)
  let hcommC := range_lsmul_comp_comm (M := M) c (a * b)
  let fA := (LinearMap.lsmul A M a) ∘ₗ (LinearMap.lsmul A M (b * c))
  let fB := (LinearMap.lsmul A M b) ∘ₗ (LinearMap.lsmul A M (a * c))
  let fC := (LinearMap.lsmul A M c) ∘ₗ (LinearMap.lsmul A M (a * b))
  let Q := M ⧸ LinearMap.range fA
  let α := periodicQuotientPhi
    (LinearMap.lsmul A M a) (LinearMap.lsmul A M (b * c)) hcommA
  let ψA := periodicQuotientPsi
    (LinearMap.lsmul A M a) (LinearMap.lsmul A M (b * c)) hcommA
  let β : Q →ₗ[A] Q := LinearMap.lsmul A Q b
  let γ : Q →ₗ[A] Q := LinearMap.lsmul A Q c
  let φB := periodicQuotientPhi
    (LinearMap.lsmul A M b) (LinearMap.lsmul A M (a * c)) hcommB
  let ψB := periodicQuotientPsi
    (LinearMap.lsmul A M b) (LinearMap.lsmul A M (a * c)) hcommB
  let φC := periodicQuotientPhi
    (LinearMap.lsmul A M c) (LinearMap.lsmul A M (a * b)) hcommC
  let ψC := periodicQuotientPsi
    (LinearMap.lsmul A M c) (LinearMap.lsmul A M (a * b)) hcommC
  have hdenA : LinearMap.range
      ((LinearMap.lsmul A M a) ∘ₗ (LinearMap.lsmul A M (b * c))) =
        LinearMap.range fA := rfl
  have hden : ∀ u v : A, u * v = a * (b * c) →
      LinearMap.range ((LinearMap.lsmul A M u) ∘ₗ (LinearMap.lsmul A M v)) =
        LinearMap.range fA := by
    intro u v huv
    congr 1
    ext x
    show u • (v • x) = a • ((b * c) • x)
    rw [smul_smul, smul_smul, huv]
  have hdenB := hden b (a * c) (by ring)
  have hdenC := hden c (a * b) (by ring)
  let eB : (M ⧸ LinearMap.range fB) ≃ₗ[A] Q := Submodule.quotEquivOfEq _ _ hdenB
  let eC : (M ⧸ LinearMap.range fC) ≃ₗ[A] Q := Submodule.quotEquivOfEq _ _ hdenC
  have hψA : ψA = β.comp γ := by
    ext x
    show Submodule.Quotient.mk ((b * c) • x) =
      Submodule.Quotient.mk (b • (c • x))
    rw [smul_smul]
  have hαγ : α.comp γ = γ.comp α := by
    ext x
    show Submodule.Quotient.mk (a • (c • x)) =
      Submodule.Quotient.mk (c • (a • x))
    rw [smul_comm]
  have hαβ : α.comp β = β.comp α := by
    ext x
    show Submodule.Quotient.mk (a • (b • x)) =
      Submodule.Quotient.mk (b • (a • x))
    rw [smul_comm]
  have hβγ : β.comp γ = γ.comp β := by
    ext x
    show Submodule.Quotient.mk (b • (c • x)) =
      Submodule.Quotient.mk (c • (b • x))
    rw [smul_comm]
  have hA : Function.Exact α (β.comp γ) := by
    rw [← hψA]
    exact exact_mul_left_right (M := M) a (b * c) (hb.mul hc)
  have hA' : Function.Exact (β.comp γ) α := by
    rw [← hψA]
    exact exact_mul_right_left (M := M) a (b * c) ha
  have hBφ : eB.toLinearMap.comp φB = β.comp eB.toLinearMap := by
    ext x
    show Submodule.Quotient.mk (b • x) = Submodule.Quotient.mk (b • x)
    rfl
  have hBψ : eB.toLinearMap.comp ψB = (α.comp γ).comp eB.toLinearMap := by
    ext x
    show Submodule.Quotient.mk ((a * c) • x) =
      Submodule.Quotient.mk (a • (c • x))
    rw [smul_smul]
  have hB := exact_of_linearEquiv eB φB ψB β (α.comp γ) hBφ hBψ
    (exact_mul_left_right (M := M) b (a * c) (ha.mul hc))
  have hB' := exact_of_linearEquiv eB ψB φB (α.comp γ) β hBψ hBφ
    (exact_mul_right_left (M := M) b (a * c) hb)
  have hCφ : eC.toLinearMap.comp φC = γ.comp eC.toLinearMap := by
    ext x
    show Submodule.Quotient.mk (c • x) = Submodule.Quotient.mk (c • x)
    rfl
  have hCψ : eC.toLinearMap.comp ψC = (α.comp β).comp eC.toLinearMap := by
    ext x
    show Submodule.Quotient.mk ((a * b) • x) =
      Submodule.Quotient.mk (a • (b • x))
    rw [smul_smul]
  have hC := exact_of_linearEquiv eC φC ψC γ (α.comp β) hCφ hCψ
    (exact_mul_left_right (M := M) c (a * b) (ha.mul hb))
  have hC' := exact_of_linearEquiv eC ψC φC (α.comp β) γ hCψ hCφ
    (exact_mul_right_left (M := M) c (a * b) hc)
  have hComplementary : ComplementaryImagesKernels α β γ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (LinearMap.exact_iff.mp hA).symm
    · simpa [hβγ] using (LinearMap.exact_iff.mp hA).symm
    · exact (LinearMap.exact_iff.mp hB).symm
    · simpa [hαγ] using (LinearMap.exact_iff.mp hB).symm
    · exact (LinearMap.exact_iff.mp hC).symm
    · simpa [hαβ] using (LinearMap.exact_iff.mp hC).symm
    · exact LinearMap.exact_iff.mp hA'
    · simpa [hβγ] using LinearMap.exact_iff.mp hA'
    · exact LinearMap.exact_iff.mp hB'
    · simpa [hαγ] using LinearMap.exact_iff.mp hB'
    · exact LinearMap.exact_iff.mp hC'
    · simpa [hαβ] using LinearMap.exact_iff.mp hC'
  have hfinite : IsFiniteLength A Q :=
    isFiniteLength_quotient_mul (M := M) a (b * c) ha (hb.mul hc) hdim
  have hdet := periodicDeterminant_mul α β γ hfinite hComplementary
  let fab : M →ₗ[A] M := (LinearMap.lsmul A M a) ∘ₗ (LinearMap.lsmul A M b)
  let Xab := M ⧸ LinearMap.range fab
  let hcommAB := range_lsmul_comp_comm (M := M) a b
  let φab := periodicQuotientPhi (LinearMap.lsmul A M a) (LinearMap.lsmul A M b) hcommAB
  let ψab := periodicQuotientPsi (LinearMap.lsmul A M a) (LinearMap.lsmul A M b) hcommAB
  have hprod : (LinearMap.lsmul A M c) ∘ₗ fab = fA := by
    ext x
    simp only [LinearMap.comp_apply, LinearMap.lsmul_apply, fab, fA, smul_smul]
    rw [show c * (a * b) = a * (b * c) by ring]
  have hpres : LinearMap.range fab ≤
      (LinearMap.range fA).comap (LinearMap.lsmul A M c) := by
    intro x hx
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hx
    refine ⟨m, ?_⟩
    exact (congrArg (fun g : M →ₗ[A] M => g m) hprod).symm
  let qC := (LinearMap.range fab).mapQ (LinearMap.range fA)
    (LinearMap.lsmul A M c) hpres
  let i := qC.codRestrict (LinearMap.range γ) (by
    intro x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range fab) x
    refine ⟨Submodule.Quotient.mk m, ?_⟩
    show γ (Submodule.Quotient.mk m) = qC (Submodule.Quotient.mk m)
    simp only [γ, qC, LinearMap.lsmul_apply, Submodule.Quotient.mk_smul,
      Submodule.mapQ_apply])
  have hi : Function.Injective i := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm
    · intro x hx
      obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range fab) x
      have hq0 : qC (Submodule.Quotient.mk m) = 0 := by
        have hv := congrArg (fun z : LinearMap.range γ => (z : Q)) hx
        simpa [i] using hv
      have hm' : (LinearMap.lsmul A M c) m ∈ LinearMap.range fA := by
        have hq0' : (Submodule.Quotient.mk ((LinearMap.lsmul A M c) m) : Q) = 0 := by
          simpa only [qC, Submodule.mapQ_apply] using hq0
        exact (Submodule.Quotient.mk_eq_zero (LinearMap.range fA)).mp hq0'
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hm'
      have hcancel : c • m = c • (fab y) := by
        calc
          c • m = fA y := hy.symm
          _ = c • fab y := (congrArg (fun g : M →ₗ[A] M => g y) hprod).symm
      have hm : m = fab y := hc hcancel
      have hmrange : m ∈ LinearMap.range fab := LinearMap.mem_range.mpr ⟨y, hm.symm⟩
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range fab)).mpr hmrange
    · exact bot_le
  have hisurj : Function.Surjective i := by
    intro y
    obtain ⟨q, hq⟩ := y.2
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range fA) q
    refine ⟨Submodule.Quotient.mk m, ?_⟩
    apply Subtype.ext
    calc
      qC (Submodule.Quotient.mk m) = Submodule.Quotient.mk (c • m) := by simp [qC]
      _ = γ (Submodule.Quotient.mk m) := by simp [γ]
      _ = y := hq
  let e1 : Xab ≃ₗ[A] LinearMap.range γ := LinearEquiv.ofBijective i ⟨hi, hisurj⟩
  have he1 : e1.toLinearMap = i := by
    ext x
    simpa [e1] using
      (LinearEquiv.ofBijective_apply i (hf := ⟨hi, hisurj⟩) (Submodule.Quotient.mk x))
  have hiφ : e1.toLinearMap.comp φab =
      (alphaOnGammaRange α β γ hComplementary).comp e1.toLinearMap := by
    rw [he1]
    ext m
    show Submodule.Quotient.mk (c • (a • m)) = Submodule.Quotient.mk (a • (c • m))
    exact congrArg _ (smul_comm c a m)
  have hiψ : e1.toLinearMap.comp ψab =
      (betaOnGammaRange α β γ hComplementary).comp e1.toLinearMap := by
    rw [he1]
    ext m
    show Submodule.Quotient.mk (c • (b • m)) = Submodule.Quotient.mk (b • (c • m))
    rw [smul_comm]
  have hSymAB : moduleSymbol a b ha hb hdim =
      periodicDeterminant φab ψab
        (exact_mul_left_right (M := M) a b hb)
        (exact_mul_right_left (M := M) a b ha)
        (isFiniteLength_quotient_mul (M := M) a b ha hb hdim) := by
    simp [moduleSymbol, φab, ψab]
  have hfactor1 := periodicDeterminant_eq_of_linearEquiv φab ψab
    (exact_mul_left_right (M := M) a b hb)
    (exact_mul_right_left (M := M) a b ha)
    (alphaOnGammaRange α β γ hComplementary)
    (betaOnGammaRange α β γ hComplementary)
    (exact_alpha_beta_onGammaRange α β γ hComplementary)
    (exact_beta_alpha_onGammaRange α β γ hComplementary)
    e1 hiφ hiψ
    (isFiniteLength_quotient_mul (M := M) a b ha hb hdim)
    (hfinite.of_injective (LinearMap.range γ).subtype_injective)
  let gac : M →ₗ[A] M := (LinearMap.lsmul A M a) ∘ₗ (LinearMap.lsmul A M c)
  let Xac := M ⧸ LinearMap.range gac
  let hcommAC := range_lsmul_comp_comm (M := M) a c
  let φac := periodicQuotientPhi (LinearMap.lsmul A M a) (LinearMap.lsmul A M c) hcommAC
  let ψac := periodicQuotientPsi (LinearMap.lsmul A M a) (LinearMap.lsmul A M c) hcommAC
  have hincAC : LinearMap.range fA ≤
      (LinearMap.range gac).comap (LinearMap.id : M →ₗ[A] M) := by
    intro x hx
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.mp hx
    refine ⟨b • m, ?_⟩
    show a • (c • (b • m)) = a • ((b * c) • m)
    simp only [smul_smul]
    rw [show a * (c * b) = a * (b * c) by ring]
  let qac := (LinearMap.range fA).mapQ (LinearMap.range gac)
    (LinearMap.id : M →ₗ[A] M) hincAC
  have hqacSurj : Function.Surjective qac := by
    intro x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range gac) x
    exact ⟨Submodule.Quotient.mk m, by simp [qac, Submodule.mapQ_apply]⟩
  have hqacAlpha : qac.comp α = φac.comp qac := by
    ext m
    simp [qac, α, φac, periodicQuotientPhi,
      Submodule.mapQ_apply, LinearMap.comp_apply, LinearMap.lsmul_apply]
  have hqacGamma : qac.comp γ = ψac.comp qac := by
    ext m
    show qac (c • (Submodule.Quotient.mk m)) = c • qac (Submodule.Quotient.mk m)
    exact map_smul qac c (Submodule.Quotient.mk m)
  have hrangeKill : LinearMap.range (α.comp γ) ≤ LinearMap.ker qac := by
    intro x hx
    obtain ⟨q, rfl⟩ := LinearMap.mem_range.mp hx
    apply LinearMap.mem_ker.mpr
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range fA) q
    have hαγ : qac (α (γ (Submodule.Quotient.mk m))) =
        φac (ψac (qac (Submodule.Quotient.mk m))) := by
      calc
        qac (α (γ (Submodule.Quotient.mk m))) =
            φac (qac (γ (Submodule.Quotient.mk m))) :=
              congrArg (fun f => f (γ (Submodule.Quotient.mk m))) hqacAlpha
        _ = φac (ψac (qac (Submodule.Quotient.mk m))) := by
              rw [show qac (γ (Submodule.Quotient.mk m)) =
                ψac (qac (Submodule.Quotient.mk m)) from
                  congrArg (fun f => f (Submodule.Quotient.mk m)) hqacGamma]
    have hzero : φac (ψac (qac (Submodule.Quotient.mk m))) = 0 := by
      show (Submodule.Quotient.mk (gac m) : Xac) = 0
      apply (Submodule.Quotient.mk_eq_zero (LinearMap.range gac)).mpr
      exact LinearMap.mem_range_self gac m
    exact hαγ.trans hzero
  have hkerBetaLe : LinearMap.ker β ≤ LinearMap.ker qac := by
    rw [hComplementary.ker_beta_eq_range_alpha_gamma]
    exact hrangeKill
  have hBprod : (LinearMap.lsmul A M b) ∘ₗ gac = fB := by
    ext m
    simp only [gac, fB, LinearMap.comp_apply, LinearMap.lsmul_apply, smul_smul]
  have hkerQacLe : LinearMap.ker qac ≤ LinearMap.ker β := by
    intro q hq
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range fA) q
    apply LinearMap.mem_ker.mpr
    have hmem : m ∈ LinearMap.range gac := by
      have hq' : (Submodule.Quotient.mk m : Xac) = 0 := by
        simpa [qac, Submodule.mapQ_apply] using hq
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range gac)).mp hq'
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
    have hbmem : (LinearMap.lsmul A M b) m ∈ LinearMap.range fA := by
      rw [← hdenB]
      refine ⟨y, ?_⟩
      rw [← hy]
      exact (congrArg (fun f : M →ₗ[A] M => f y) hBprod).symm
    show (Submodule.Quotient.mk ((LinearMap.lsmul A M b) m) : Q) = 0
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range fA)).mpr hbmem
  let e2fun := (LinearMap.ker β).liftQ qac hkerBetaLe
  have hkerEq : LinearMap.ker β = LinearMap.ker qac := le_antisymm hkerBetaLe hkerQacLe
  have he2funInj : Function.Injective e2fun :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' (LinearMap.ker β) qac hkerEq)
  have he2funSurj : Function.Surjective e2fun := by
    intro x
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range gac) x
    refine ⟨Submodule.Quotient.mk (Submodule.Quotient.mk m), ?_⟩
    show e2fun (Submodule.Quotient.mk (Submodule.Quotient.mk m)) =
      Submodule.Quotient.mk m
    simp only [e2fun, Submodule.liftQ_apply]
    show (Submodule.Quotient.mk ((LinearMap.id : M →ₗ[A] M) m) : Xac) =
      Submodule.Quotient.mk m
    rfl
  let e2 : (Q ⧸ LinearMap.ker β) ≃ₗ[A] Xac :=
    LinearEquiv.ofBijective e2fun ⟨he2funInj, he2funSurj⟩
  have he2 : e2.toLinearMap = e2fun := by
    ext m
    simpa [e2] using
      (LinearEquiv.ofBijective_apply e2fun (hf := ⟨he2funInj, he2funSurj⟩)
        (Submodule.Quotient.mk (Submodule.Quotient.mk m)))
  let φker := alphaOnKerBetaQuotient α β γ hComplementary
  let ψker := gammaOnKerBetaQuotient α β γ hComplementary
  have he2φ : e2.toLinearMap.comp φker = φac.comp e2.toLinearMap := by
    rw [he2]
    ext q
    show qac (α (Submodule.Quotient.mk q)) = φac (qac (Submodule.Quotient.mk q))
    exact congrArg (fun f => f (Submodule.Quotient.mk q)) hqacAlpha
  have he2ψ : e2.toLinearMap.comp ψker = ψac.comp e2.toLinearMap := by
    rw [he2]
    ext q
    show qac (γ (Submodule.Quotient.mk q)) = ψac (qac (Submodule.Quotient.mk q))
    exact congrArg (fun f => f (Submodule.Quotient.mk q)) hqacGamma
  have hSymAC : moduleSymbol a c ha hc hdim =
      periodicDeterminant φac ψac
        (exact_mul_left_right (M := M) a c hc)
        (exact_mul_right_left (M := M) a c ha)
        (isFiniteLength_quotient_mul (M := M) a c ha hc hdim) := by
    simp [moduleSymbol, φac, ψac]
  have hfactor2 := periodicDeterminant_eq_of_linearEquiv
    φker ψker
    (by simpa [φker, ψker] using
      exact_alpha_gamma_onKerBetaQuotient α β γ hComplementary)
    (by simpa [φker, ψker] using
      exact_gamma_alpha_onKerBetaQuotient α β γ hComplementary)
    φac ψac
    (exact_mul_left_right (M := M) a c hc)
    (exact_mul_right_left (M := M) a c ha)
    e2 he2φ he2ψ
    (hfinite.of_surjective (Submodule.mkQ_surjective (LinearMap.ker β)))
    (isFiniteLength_quotient_mul (M := M) a c ha hc hdim)
  have hSymABC : moduleSymbol a (b * c) ha (hb.mul hc) hdim =
      periodicDeterminant α (β ∘ₗ γ)
        (exact_alpha_betaGamma α β γ hComplementary)
        (exact_betaGamma_alpha α β γ hComplementary) hfinite := by
    simp [moduleSymbol, α, ψA, hψA]
  calc
    moduleSymbol a (b * c) ha (hb.mul hc) hdim =
        periodicDeterminant α (β ∘ₗ γ)
          (exact_alpha_betaGamma α β γ hComplementary)
          (exact_betaGamma_alpha α β γ hComplementary) hfinite := hSymABC
    _ = periodicDeterminant (alphaOnGammaRange α β γ hComplementary)
          (betaOnGammaRange α β γ hComplementary)
          (exact_alpha_beta_onGammaRange α β γ hComplementary)
          (exact_beta_alpha_onGammaRange α β γ hComplementary)
          (hfinite.of_injective (LinearMap.range γ).subtype_injective) *
        periodicDeterminant φker ψker
          (exact_alpha_gamma_onKerBetaQuotient α β γ hComplementary)
          (exact_gamma_alpha_onKerBetaQuotient α β γ hComplementary)
          (hfinite.of_surjective (Submodule.mkQ_surjective (LinearMap.ker β))) := hdet
    _ = moduleSymbol a b ha hb hdim * moduleSymbol a c ha hc hdim := by
      rw [(hSymAB.trans hfactor1).symm, hfactor2, hSymAC]

/-- **Stacks Project, Tag 02Q0.** Swapping the two arguments gives inverse symbols. -/
@[stacks 02Q0 "swapped-arguments identity"]
theorem moduleSymbol_mul_swap
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    moduleSymbol a b ha hb hdim * moduleSymbol b a hb ha hdim = 1 := by
  simp only [moduleSymbol]
  let e : (M ⧸ LinearMap.range ((LinearMap.lsmul A M b) ∘ₗ
      (LinearMap.lsmul A M a))) ≃ₗ[A]
      (M ⧸ LinearMap.range ((LinearMap.lsmul A M a) ∘ₗ
        (LinearMap.lsmul A M b))) :=
    Submodule.quotEquivOfEq _ _ (range_lsmul_comp_comm (M := M) b a)
  let φba := periodicQuotientPhi
    (LinearMap.lsmul A M b) (LinearMap.lsmul A M a) (range_lsmul_comp_comm b a)
  let ψba := periodicQuotientPsi
    (LinearMap.lsmul A M b) (LinearMap.lsmul A M a) (range_lsmul_comp_comm b a)
  let φab := periodicQuotientPhi
    (LinearMap.lsmul A M a) (LinearMap.lsmul A M b) (range_lsmul_comp_comm a b)
  let ψab := periodicQuotientPsi
    (LinearMap.lsmul A M a) (LinearMap.lsmul A M b) (range_lsmul_comp_comm a b)
  have hφ : e.toLinearMap.comp φba = ψab.comp e.toLinearMap := by
    ext x
    simp [e, φba, ψab, periodicQuotientPhi, periodicQuotientPsi]
  have hψ : e.toLinearMap.comp ψba = φab.comp e.toLinearMap := by
    ext x
    simp [e, ψba, φab, periodicQuotientPhi, periodicQuotientPsi]
  have h := periodicDeterminant_mul_swap
    φba ψba
    (exact_mul_left_right b a ha)
    (exact_mul_right_left b a hb)
    (isFiniteLength_quotient_mul b a hb ha hdim)
  have htransport := periodicDeterminant_eq_of_linearEquiv
    ψba φba (exact_mul_right_left b a hb)
    (exact_mul_left_right b a ha)
    φab ψab (exact_mul_left_right a b hb)
    (exact_mul_right_left a b ha)
    e hψ hφ
    (isFiniteLength_quotient_mul b a hb ha hdim)
    (isFiniteLength_quotient_mul a b ha hb hdim)
  rw [htransport] at h
  simpa [mul_comm, φab, ψab] using h

end AlgebraicGeometry
