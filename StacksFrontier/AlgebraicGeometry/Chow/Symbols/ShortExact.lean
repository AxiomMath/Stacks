module

public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.ShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.Basic

/-!
# The symbol in a short exact sequence

For a short exact sequence of finite modules of support dimension one over a Noetherian local
ring, the symbol of two common nonzerodivisors is multiplicative.

## Main results

* `AlgebraicGeometry.moduleSymbol_short_exact` gives multiplicativity of the symbol across a
  short exact sequence.

## Implementation notes

The short exact sequence is given by linear maps with injectivity, surjectivity and exactness
at the middle module. The support dimension and regularity hypotheses are stated for all three
modules, as in the source.

## References

* [Stacks Project, Tag 02Q3](https://stacks.math.columbia.edu/tag/02Q3)
-/

@[expose] public section

namespace AlgebraicGeometry

universe u v₁ v₂ v₃

/-- A short exact sequence compatible with three endomorphisms induces a short exact sequence on
the quotients by their images. -/
private theorem quotient_short_exact
    {R : Type u} [Ring R]
    {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₁) (f₂ : M₂ →ₗ[R] M₂) (f₃ : M₃ →ₗ[R] M₃)
    (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (hfi : f₂.comp i = i.comp f₁) (hfp : f₃.comp p = p.comp f₂)
    (hf₃ : Function.Injective f₃) :
    Function.Injective
        (Submodule.mapQ (LinearMap.range f₁) (LinearMap.range f₂) i (by
          intro x hx
          obtain ⟨y, rfl⟩ := hx
          exact ⟨i y, congrArg (fun g : M₁ →ₗ[R] M₂ => g y) hfi⟩)) ∧
      Function.Surjective
        (Submodule.mapQ (LinearMap.range f₂) (LinearMap.range f₃) p (by
          intro x hx
          obtain ⟨y, rfl⟩ := hx
          exact ⟨p y, congrArg (fun g : M₂ →ₗ[R] M₃ => g y) hfp⟩)) ∧
      Function.Exact
        (Submodule.mapQ (LinearMap.range f₁) (LinearMap.range f₂) i (by
          intro x hx
          obtain ⟨y, rfl⟩ := hx
          exact ⟨i y, congrArg (fun g : M₁ →ₗ[R] M₂ => g y) hfi⟩))
        (Submodule.mapQ (LinearMap.range f₂) (LinearMap.range f₃) p (by
          intro x hx
          obtain ⟨y, rfl⟩ := hx
          exact ⟨p y, congrArg (fun g : M₂ →ₗ[R] M₃ => g y) hfp⟩)) := by
  let iQ := Submodule.mapQ (LinearMap.range f₁) (LinearMap.range f₂) i (by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨i y, congrArg (fun g : M₁ →ₗ[R] M₂ => g y) hfi⟩)
  let pQ := Submodule.mapQ (LinearMap.range f₂) (LinearMap.range f₃) p (by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨p y, congrArg (fun g : M₂ →ₗ[R] M₃ => g y) hfp⟩)
  have hiQ : Function.Injective iQ := by
    intro q q' hqq
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      induction q' using Submodule.Quotient.induction_on with
      | _ y =>
        have hmem : i (x - y) ∈ LinearMap.range f₂ := by
          rw [map_sub]
          exact (Submodule.Quotient.eq _).mp (by simpa [iQ] using hqq)
        obtain ⟨z, hz⟩ := hmem
        have hpz : p z = 0 := hf₃ (by
          calc
            f₃ (p z) = p (f₂ z) := congrArg (fun g : M₂ →ₗ[R] M₃ => g z) hfp
            _ = p (i (x - y)) := by rw [hz]
            _ = f₃ 0 := by
              rw [map_zero]
              exact (hip (i (x - y))).2 ⟨x - y, rfl⟩)
        obtain ⟨w, hw⟩ := (hip z).mp hpz
        have hxy : x - y = f₁ w := hi (by
          calc
            i (x - y) = f₂ z := hz.symm
            _ = f₂ (i w) := by rw [hw]
            _ = i (f₁ w) := congrArg (fun g : M₁ →ₗ[R] M₂ => g w) hfi)
        exact (Submodule.Quotient.eq _).mpr ⟨w, hxy.symm⟩
  have hpQ : Function.Surjective pQ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ z =>
      obtain ⟨y, rfl⟩ := hp z
      exact ⟨Submodule.Quotient.mk y, by simp [pQ, Submodule.mapQ_apply]⟩
  have hipQ : Function.Exact iQ pQ := by
    intro q
    constructor
    · intro hq
      induction q using Submodule.Quotient.induction_on with
      | _ y =>
        change (Submodule.Quotient.mk (p y) : M₃ ⧸ LinearMap.range f₃) = 0 at hq
        rw [Submodule.Quotient.mk_eq_zero] at hq
        obtain ⟨z, hz⟩ := hq
        obtain ⟨y', hy'⟩ := hp z
        have hyker : p (y - f₂ y') = 0 := by
          have hcompat : f₃ (p y') = p (f₂ y') :=
            congrArg (fun g : M₂ →ₗ[R] M₃ => g y') hfp
          rw [map_sub, ← hcompat, ← hz, hy', sub_self]
        obtain ⟨x, hx⟩ := (hip (y - f₂ y')).mp hyker
        refine ⟨Submodule.Quotient.mk x, ?_⟩
        have hy'' : y = i x + f₂ y' := by rw [hx]; abel
        change Submodule.Quotient.mk (i x) = Submodule.Quotient.mk y
        rw [hy'', Submodule.Quotient.mk_add]
        simp
    · rintro ⟨r, rfl⟩
      induction r using Submodule.Quotient.induction_on with
      | _ x =>
        change (Submodule.Quotient.mk (p (i x)) : M₃ ⧸ LinearMap.range f₃) = 0
        have hpi : p (i x) = 0 := (hip (i x)).2 ⟨x, rfl⟩
        rw [hpi]
        simp
  exact ⟨hiQ, hpQ, hipQ⟩

/-- **Stacks Project, Tag 02Q3.** The symbol of the middle term of a short exact sequence is
the product of the symbols of its outer terms. -/
@[stacks 02Q3]
theorem moduleSymbol_short_exact
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type v₁} {M' : Type v₂} {M'' : Type v₃}
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup M'] [Module A M'] [Module.Finite A M']
    [AddCommGroup M''] [Module A M''] [Module.Finite A M'']
    (i : M →ₗ[A] M') (p : M' →ₗ[A] M'')
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (a b : A)
    (haM : IsSMulRegular M a) (hbM : IsSMulRegular M b)
    (haM' : IsSMulRegular M' a) (hbM' : IsSMulRegular M' b)
    (haM'' : IsSMulRegular M'' a) (hbM'' : IsSMulRegular M'' b)
    (hdimM : Module.supportDim A M = 1)
    (hdimM' : Module.supportDim A M' = 1)
    (hdimM'' : Module.supportDim A M'' = 1) :
    moduleSymbol a b haM' hbM' hdimM' =
      moduleSymbol a b haM hbM hdimM * moduleSymbol a b haM'' hbM'' hdimM'' := by
  let φ₁ : M →ₗ[A] M := LinearMap.lsmul A M a
  let ψ₁ : M →ₗ[A] M := LinearMap.lsmul A M b
  let φ₂ : M' →ₗ[A] M' := LinearMap.lsmul A M' a
  let ψ₂ : M' →ₗ[A] M' := LinearMap.lsmul A M' b
  let φ₃ : M'' →ₗ[A] M'' := LinearMap.lsmul A M'' a
  let ψ₃ : M'' →ₗ[A] M'' := LinearMap.lsmul A M'' b
  let f₁ := φ₁.comp ψ₁
  let f₂ := φ₂.comp ψ₂
  let f₃ := φ₃.comp ψ₃
  have hφiM : φ₂.comp i = i.comp φ₁ := by
    ext x
    simp [φ₁, φ₂]
  have hψiM : ψ₂.comp i = i.comp ψ₁ := by
    ext x
    simp [ψ₁, ψ₂]
  have hφpM : φ₃.comp p = p.comp φ₂ := by
    ext x
    simp [φ₂, φ₃]
  have hψpM : ψ₃.comp p = p.comp ψ₂ := by
    ext x
    simp [ψ₂, ψ₃]
  have hfi : f₂.comp i = i.comp f₁ := by
    ext x
    simp [f₁, f₂, φ₁, ψ₁, φ₂, ψ₂]
  have hfp : f₃.comp p = p.comp f₂ := by
    ext x
    simp [f₂, f₃, φ₂, ψ₂, φ₃, ψ₃]
  have hquot := quotient_short_exact f₁ f₂ f₃ i p hi hp hip hfi hfp
    (haM''.comp hbM'')
  let iQ := Submodule.mapQ (LinearMap.range f₁) (LinearMap.range f₂) i (by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨i y, by
      simpa [LinearMap.comp_apply] using
        (congrArg (fun g : M →ₗ[A] M' => g y) hfi)⟩)
  let pQ := Submodule.mapQ (LinearMap.range f₂) (LinearMap.range f₃) p (by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨p y, by
      simpa [LinearMap.comp_apply] using
        (congrArg (fun g : M' →ₗ[A] M'' => g y) hfp)⟩)
  have hcomm₁ := range_lsmul_comp_comm (M := M) a b
  have hcomm₂ := range_lsmul_comp_comm (M := M') a b
  have hcomm₃ := range_lsmul_comp_comm (M := M'') a b
  let φQ₁ := periodicQuotientPhi φ₁ ψ₁ hcomm₁
  let ψQ₁ := periodicQuotientPsi φ₁ ψ₁ hcomm₁
  let φQ₂ := periodicQuotientPhi φ₂ ψ₂ hcomm₂
  let ψQ₂ := periodicQuotientPsi φ₂ ψ₂ hcomm₂
  let φQ₃ := periodicQuotientPhi φ₃ ψ₃ hcomm₃
  let ψQ₃ := periodicQuotientPsi φ₃ ψ₃ hcomm₃
  have hφi : φQ₂.comp iQ = iQ.comp φQ₁ := by
    ext x
    exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun hφiM x)
  have hψi : ψQ₂.comp iQ = iQ.comp ψQ₁ := by
    ext x
    exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun hψiM x)
  have hφp : φQ₃.comp pQ = pQ.comp φQ₂ := by
    ext x
    exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun hφpM x)
  have hψp : ψQ₃.comp pQ = pQ.comp ψQ₂ := by
    ext x
    exact congrArg Submodule.Quotient.mk (LinearMap.congr_fun hψpM x)
  simpa [moduleSymbol] using
    (periodicDeterminant_short_exact φQ₁ ψQ₁ φQ₂ ψQ₂ φQ₃ ψQ₃ iQ pQ hquot.1 hquot.2.1 hquot.2.2
      hφi hψi hφp hψp
      (exact_mul_left_right a b hbM) (exact_mul_right_left a b haM)
      (exact_mul_left_right a b hbM') (exact_mul_right_left a b haM')
      (exact_mul_left_right a b hbM'') (exact_mul_right_left a b haM'')
      (isFiniteLength_quotient_mul a b haM hbM hdimM)
      (isFiniteLength_quotient_mul a b haM' hbM' hdimM')
      (isFiniteLength_quotient_mul a b haM'' hbM'' hdimM''))

end AlgebraicGeometry
