module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.UnitScaling
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Multiplicativity
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.ShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Sign
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.MinimalPrimes

/-!
# The symbol of two regular elements of a finite algebra

Let `R` be a Noetherian local ring and `S` a finite `R`-algebra of support dimension one. For two
regular elements `a, b` of `S` the periodic determinant over `R` of the two-periodic complex
`(S / abS, a, b)` is a unit of the residue field of `R`: the `d^R_S(a, b)` of the proof of Stacks
02Q8. For `a, b` in `R` it is the module symbol `d_S(a, b)` of Stacks 02PZ. This file proves that
the symbol is multiplicative in the second argument, is inverted by swapping the arguments, takes
a sign on a repeated argument, and for two coprime elements is a ratio of residue-field
determinants of multiplications (Stacks 02PN, 02PU, 02PL, 02PM).

## Restatements of private results of the base

All of these are proved in `StacksFrontier/AlgebraicGeometry/Chow/Symbols/Steinberg.lean` (Tag 02Q8)
as `private` declarations, and so cannot be named from another module. They are restated here
under new names, with the same proofs: `Stacks.Chow.finiteAlgebraSymbol` is the private
`algebraSymbol` there, and the lemmas about it are the private lemmas about `algebraSymbol`.

## Main results

* `Stacks.Chow.finiteAlgebraSymbol_mul_right`, `Stacks.Chow.finiteAlgebraSymbol_swap`,
  `Stacks.Chow.finiteAlgebraSymbol_self`, `Stacks.Chow.finiteAlgebraSymbol_of_isCoprime`.
* `Stacks.Chow.moduleSymbol_eq_finiteAlgebraSymbol` — the module symbol of elements of `R`.

## References

* [Stacks Project, Tag 02PZ](https://stacks.math.columbia.edu/tag/02PZ)
* [Stacks Project, Tag 02Q8](https://stacks.math.columbia.edu/tag/02Q8)
-/

@[expose] public section

open CategoryTheory

open Module.FiniteLength AlgebraicGeometry

namespace Stacks.Chow

universe u v

/-- The symbol attached to two commuting injective endomorphisms of a finite module of support
dimension one: the periodic determinant of the two-periodic complex they induce on the quotient
by the image of their composite. -/
noncomputable def endoPeriodicSymbol
    {A : Type u} {E : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (α β : E →ₗ[A] E) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hR : LinearMap.range (α ∘ₗ β) = LinearMap.range (β ∘ₗ α))
    (hdim : Module.supportDim A E = 1) : (IsLocalRing.ResidueField A)ˣ :=
  periodicDeterminant (periodicQuotientPhi α β hR) (periodicQuotientPsi α β hR)
    (exact_periodicQuotient_phi_psi α β hβ hR) (exact_periodicQuotient_psi_phi α β hα hR)
    (Module.isFiniteLength_quotient_range_of_injective (α.comp β) (hα.comp hβ) hdim)

/-- For multiplications by two ring elements the symbol of the endomorphisms is the module
symbol. -/
theorem endoPeriodicSymbol_smul
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    endoPeriodicSymbol (LinearMap.lsmul A M a) (LinearMap.lsmul A M b) ha hb
        (congrArg LinearMap.range (by
          ext m
          simp only [LinearMap.comp_apply, LinearMap.lsmul_apply]
          exact smul_comm a b m)) hdim =
      moduleSymbol a b ha hb hdim := by
  rfl

/-- Interchanging the two endomorphisms inverts the symbol. -/
theorem endoPeriodicSymbol_swap
    {A : Type u} {E : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (α β : E →ₗ[A] E) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hR : LinearMap.range (α ∘ₗ β) = LinearMap.range (β ∘ₗ α))
    (hdim : Module.supportDim A E = 1) :
    endoPeriodicSymbol α β hα hβ hR hdim * endoPeriodicSymbol β α hβ hα hR.symm hdim = 1 := by
  let φ := periodicQuotientPhi α β hR
  let ψ := periodicQuotientPsi α β hR
  let φ' := periodicQuotientPhi β α hR.symm
  let ψ' := periodicQuotientPsi β α hR.symm
  let e := Submodule.quotEquivOfEq _ _ hR
  have hαβ := Module.isFiniteLength_quotient_range_of_injective (α.comp β) (hα.comp hβ) hdim
  have hβα := Module.isFiniteLength_quotient_range_of_injective (β.comp α) (hβ.comp hα) hdim
  have hcomm : e.toLinearMap.comp φ = ψ'.comp e.toLinearMap ∧
      e.toLinearMap.comp ψ = φ'.comp e.toLinearMap := by
    constructor <;>
    · apply LinearMap.ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x => simp [e, φ, ψ, φ', ψ', periodicQuotientPhi, periodicQuotientPsi,
          Submodule.quotEquivOfEq_mk]
  have htrans := periodicDeterminant_eq_of_linearEquiv ψ φ
    (exact_periodicQuotient_psi_phi α β hα hR)
    (exact_periodicQuotient_phi_psi α β hβ hR)
    φ' ψ'
    (exact_periodicQuotient_phi_psi β α hα hR.symm)
    (exact_periodicQuotient_psi_phi β α hβ hR.symm)
    e hcomm.2 hcomm.1 hαβ hβα
  have hswap := periodicDeterminant_mul_swap φ ψ
    (exact_periodicQuotient_phi_psi α β hβ hR)
    (exact_periodicQuotient_psi_phi α β hα hR) hαβ
  calc
    endoPeriodicSymbol α β hα hβ hR hdim * endoPeriodicSymbol β α hβ hα hR.symm hdim =
        periodicDeterminant φ ψ
          (exact_periodicQuotient_phi_psi α β hβ hR)
          (exact_periodicQuotient_psi_phi α β hα hR) hαβ *
        periodicDeterminant φ' ψ'
          (exact_periodicQuotient_phi_psi β α hα hR.symm)
          (exact_periodicQuotient_psi_phi β α hβ hR.symm) hβα := by
              simp [endoPeriodicSymbol, φ, ψ, φ', ψ']
    _ = 1 := by rwa [← htrans]

/-- The periodic determinant of a product of two exact two-periodic complexes is the product of
their periodic determinants. -/
theorem periodicDeterminant_prodMap
    {R : Type u} [CommRing R] [IsLocalRing R]
    {E₁ : Type v} {E₂ : Type*} [AddCommGroup E₁] [Module R E₁]
    [AddCommGroup E₂] [Module R E₂]
    (φ₁ ψ₁ : E₁ →ₗ[R] E₁) (hφ₁ψ₁ : Function.Exact φ₁ ψ₁)
    (hψ₁φ₁ : Function.Exact ψ₁ φ₁)
    (φ₂ ψ₂ : E₂ →ₗ[R] E₂) (hφ₂ψ₂ : Function.Exact φ₂ ψ₂)
    (hψ₂φ₂ : Function.Exact ψ₂ φ₂)
    (hE₁ : IsFiniteLength R E₁) (hE₂ : IsFiniteLength R E₂)
    (h : Function.Exact (φ₁.prodMap φ₂) (ψ₁.prodMap ψ₂))
    (h' : Function.Exact (ψ₁.prodMap ψ₂) (φ₁.prodMap φ₂)) (hE : IsFiniteLength R (E₁ × E₂)) :
    periodicDeterminant (φ₁.prodMap φ₂) (ψ₁.prodMap ψ₂) h h' hE =
      periodicDeterminant φ₁ ψ₁ hφ₁ψ₁ hψ₁φ₁ hE₁ *
        periodicDeterminant φ₂ ψ₂ hφ₂ψ₂ hψ₂φ₂ hE₂ := by
  apply periodicDeterminant_short_exact
    φ₁ ψ₁ (φ₁.prodMap φ₂) (ψ₁.prodMap ψ₂) φ₂ ψ₂
    (LinearMap.inl R E₁ E₂) (LinearMap.snd R E₁ E₂)
  · exact fun x y h => congrArg Prod.fst h
  · exact fun y => ⟨(0, y), rfl⟩
  · exact Function.Exact.inl_snd
  all_goals ext x <;> simp

section AlgebraQuotients

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The quotient of a ring by the ideal generated by one of its elements. -/
abbrev singletonQuotient (S : Type*) [CommRing S] (a : S) : Type _ :=
  S ⧸ (Ideal.span {a} : Ideal S)

/-- Multiplication by an element on a principal quotient, as a map of modules over the base
ring. -/
abbrev singletonQuotientMul (R : Type*) [CommRing R] {S : Type*} [CommRing S]
    [Algebra R S] (d x : S) : singletonQuotient S d →ₗ[R] singletonQuotient S d :=
  LinearMap.mulLeft R (Ideal.Quotient.mk _ x)

/-- On `S / abS`, multiplication by `a` followed by multiplication by `b` is exact. -/
theorem exact_singletonQuotientMul (a b : S) (hb : IsRegular b) :
    Function.Exact (singletonQuotientMul R (a * b) a) (singletonQuotientMul R (a * b) b) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change (Ideal.Quotient.mk _ b) * (Ideal.Quotient.mk _ x) = 0 ↔ _
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      have hx : x = a * y := hb.left (by simpa [mul_assoc, mul_left_comm] using hy)
      refine ⟨Ideal.Quotient.mk _ y, ?_⟩
      change (Ideal.Quotient.mk _ a) * (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ x
      rw [← map_mul, hx]
    · rintro ⟨y, hy⟩
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        change (Ideal.Quotient.mk _ a) * (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ x at hy
        rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
        obtain ⟨z, hz⟩ := hy
        refine ⟨y - b * z, ?_⟩
        linear_combination -b * hz

/-- The symbol of two regular elements of a finite algebra, with the determinant taken over the
base ring: the periodic determinant of the two-periodic complex of multiplications they induce
on the quotient by their product. -/
noncomputable def finiteAlgebraSymbol [IsLocalRing R]
    (a b : S) (ha : IsRegular a) (hb : IsRegular b)
    (hL : IsFiniteLength R (singletonQuotient S (a * b))) :
    (IsLocalRing.ResidueField R)ˣ :=
  periodicDeterminant (singletonQuotientMul R (a * b) a) (singletonQuotientMul R (a * b) b)
    (exact_singletonQuotientMul a b hb)
    (by
      have h := exact_singletonQuotientMul (R := R) b a ha
      rw [mul_comm b a] at h
      exact h) hL

/-- The quotient by the image of the composite of two multiplications is the quotient by the
ideal generated by the product. -/
noncomputable def singletonQuotientRangeMulEquiv (a b : S) :
    (S ⧸ (LinearMap.mulLeft R a ∘ₗ LinearMap.mulLeft R b).range) ≃ₗ[R]
      singletonQuotient S (a * b) :=
  (Submodule.quotEquivOfEq _ _ (by
      rw [← LinearMap.mulLeft_mul]
      ext x
      simp only [LinearMap.mem_range, LinearMap.mulLeft_apply,
        Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
      exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩)).trans
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {a * b}))

/-- `singletonQuotientRangeMulEquiv` sends the class of `x` to the class of `x`. -/
theorem singletonQuotientRangeMulEquiv_mk (a b x : S) :
    singletonQuotientRangeMulEquiv (R := R) a b (Submodule.Quotient.mk x) =
      Ideal.Quotient.mk _ x := rfl

/-- For a finite algebra of support dimension one over a Noetherian local ring, the quotient by
a regular element has finite length. -/
theorem isFiniteLength_singletonQuotient [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R S] (hdim : Module.supportDim R S = 1)
    (a : S) (ha : IsRegular a) : IsFiniteLength R (singletonQuotient S a) := by
  have h := Module.isFiniteLength_quotient_range_of_injective
    (LinearMap.mulLeft R a) ha.left hdim
  rw [show (LinearMap.mulLeft R a).range = (Ideal.span {a}).restrictScalars R by
    ext x
    simp only [LinearMap.mem_range, LinearMap.mulLeft_apply,
      Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩] at h
  exact (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {a})).isFiniteLength h

/-- The symbol of two multiplications is the symbol of the two elements. -/
theorem endoPeriodicSymbol_mulLeft [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R S] (hdim : Module.supportDim R S = 1)
    (a b : S) (ha : IsRegular a) (hb : IsRegular b) :
    endoPeriodicSymbol (LinearMap.mulLeft R a) (LinearMap.mulLeft R b) ha.left hb.left
        (congrArg LinearMap.range (by ext x; simp [mul_left_comm])) hdim =
      finiteAlgebraSymbol a b ha hb
        (isFiniteLength_singletonQuotient hdim (a * b) (ha.mul hb)) := by
  apply periodicDeterminant_eq_of_linearEquiv _ _ _ _ _ _ _ _
    (singletonQuotientRangeMulEquiv (R := R) a b)
  all_goals
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

/-- Multiplication by an element coprime to `a` is an automorphism of the quotient by `a`. -/
noncomputable def singletonQuotientMulEquiv (a b : S) (h : IsCoprime a b) :
    singletonQuotient S a ≃ₗ[R] singletonQuotient S a :=
  (LinearEquiv.smulOfUnit (M := singletonQuotient S a)
    (show IsUnit (Ideal.Quotient.mk (Ideal.span {a}) b) by
      simpa only [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton a)),
        isCoprime_zero_left] using
          h.map (Ideal.Quotient.mk (Ideal.span {a}))).unit).restrictScalars R

/-- `singletonQuotientMulEquiv a b h` is multiplication by `b`. -/
theorem singletonQuotientMulEquiv_apply (a b : S) (h : IsCoprime a b)
    (x : singletonQuotient S a) :
    singletonQuotientMulEquiv (R := R) a b h x = singletonQuotientMul R a b x := by
  simp [singletonQuotientMulEquiv, LinearEquiv.smulOfUnit, smul_eq_mul]

/-- The Chinese remainder theorem for two coprime elements. -/
noncomputable def singletonQuotientEquivProd (a b : S) (h : IsCoprime a b) :
    singletonQuotient S (a * b) ≃ₐ[R]
      singletonQuotient S a × singletonQuotient S b := by
  let e := (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm).trans
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      ((Ideal.isCoprime_span_singleton_iff a b).mpr h))
  exact { e with
    commutes' := fun r => by
      apply Prod.ext <;>
        simp [e, Ideal.quotientMulEquivQuotientProd_fst,
          Ideal.quotientMulEquivQuotientProd_snd, ← Ideal.Quotient.mk_algebraMap] }

/-- The Chinese remainder isomorphism sends the class of `x` to the pair of its classes. -/
theorem singletonQuotientEquivProd_mk (a b : S) (h : IsCoprime a b) (x : S) :
    singletonQuotientEquivProd (R := R) a b h (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
  apply Prod.ext <;>
    simp [singletonQuotientEquivProd, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.quotientMulEquivQuotientProd_snd]

/-- For two coprime elements the symbol is the ratio of the determinants of the two
multiplication automorphisms on the two principal quotients. -/
theorem finiteAlgebraSymbol_of_isCoprime [IsLocalRing R]
    (a b : S) (ha : IsRegular a) (hb : IsRegular b) (h : IsCoprime a b)
    (hL : IsFiniteLength R (singletonQuotient S (a * b)))
    (hLa : IsFiniteLength R (singletonQuotient S a))
    (hLb : IsFiniteLength R (singletonQuotient S b)) :
    finiteAlgebraSymbol a b ha hb hL =
      (determinantAutomorphism (singletonQuotientMulEquiv (R := R) a b h) hLa)⁻¹ *
        determinantAutomorphism (singletonQuotientMulEquiv (R := R) b a h.symm) hLb := by
  let ea := singletonQuotientMulEquiv (R := R) a b h
  let eb := singletonQuotientMulEquiv (R := R) b a h.symm
  let e := (singletonQuotientEquivProd (R := R) a b h).toLinearEquiv
  have he_mul (x y : singletonQuotient S (a * b)) : e (x * y) = e x * e y :=
    (singletonQuotientEquivProd (R := R) a b h).map_mul x y
  have hea : e (Ideal.Quotient.mk _ a) = (0, Ideal.Quotient.mk _ a) := by
    change singletonQuotientEquivProd (R := R) a b h (Ideal.Quotient.mk _ a) = _
    rw [singletonQuotientEquivProd_mk]
    simp
  have heb : e (Ideal.Quotient.mk _ b) = (Ideal.Quotient.mk _ b, 0) := by
    change singletonQuotientEquivProd (R := R) a b h (Ideal.Quotient.mk _ b) = _
    rw [singletonQuotientEquivProd_mk]
    simp
  have h0ea : Function.Exact (0 : Module.End R (singletonQuotient S a)) ea.toLinearMap :=
    (LinearMap.exact_zero_iff_injective _ _).2 ea.injective
  have hea0 : Function.Exact ea.toLinearMap (0 : Module.End R (singletonQuotient S a)) :=
    (LinearMap.exact_zero_iff_surjective _ _).2 ea.surjective
  have heb0 : Function.Exact eb.toLinearMap (0 : Module.End R (singletonQuotient S b)) :=
    (LinearMap.exact_zero_iff_surjective _ _).2 eb.surjective
  have h0eb : Function.Exact (0 : Module.End R (singletonQuotient S b)) eb.toLinearMap :=
    (LinearMap.exact_zero_iff_injective _ _).2 eb.injective
  have hφ : e.toLinearMap.comp (singletonQuotientMul R (a * b) a) =
      ((0 : Module.End R (singletonQuotient S a)).prodMap eb.toLinearMap).comp
        e.toLinearMap := by
    apply LinearMap.ext
    intro x
    dsimp only [LinearMap.comp_apply, singletonQuotientMul, LinearMap.mulLeft_apply,
      LinearMap.prodMap_apply, LinearMap.zero_apply, LinearEquiv.coe_coe]
    rw [he_mul, hea]
    simp only [Prod.mul_def, zero_mul]
    rfl
  have hψ : e.toLinearMap.comp (singletonQuotientMul R (a * b) b) =
      (ea.toLinearMap.prodMap (0 : Module.End R (singletonQuotient S b))).comp
        e.toLinearMap := by
    apply LinearMap.ext
    intro x
    dsimp only [LinearMap.comp_apply, singletonQuotientMul, LinearMap.mulLeft_apply,
      LinearMap.prodMap_apply, LinearMap.zero_apply, LinearEquiv.coe_coe]
    rw [he_mul, heb]
    simp only [Prod.mul_def]
    simp [ea, singletonQuotientMulEquiv_apply, singletonQuotientMul]
  have exProd : ∀ (φ₁ ψ₁ : Module.End R (singletonQuotient S a))
      (φ₂ ψ₂ : Module.End R (singletonQuotient S b)), Function.Exact φ₁ ψ₁ →
      Function.Exact φ₂ ψ₂ → Function.Exact (φ₁.prodMap φ₂) (ψ₁.prodMap ψ₂) := by
    intro φ₁ ψ₁ φ₂ ψ₂ h₁ h₂ x
    change (ψ₁ x.1, ψ₂ x.2) = (0, 0) ↔ ∃ y : _ × _, (φ₁ y.1, φ₂ y.2) = x
    rw [Prod.mk.injEq, h₁, h₂]
    exact ⟨fun ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩ => ⟨(y₁, y₂), Prod.ext hy₁ hy₂⟩,
      fun ⟨y, hy⟩ => ⟨⟨y.1, congrArg Prod.fst hy⟩, ⟨y.2, congrArg Prod.snd hy⟩⟩⟩
  have hex₁ := exProd _ _ _ _ h0ea heb0
  have hex₂ := exProd _ _ _ _ hea0 h0eb
  have hLab : IsFiniteLength R (singletonQuotient S a × singletonQuotient S b) := by
    obtain ⟨hN₁, hA₁⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hLa
    obtain ⟨hN₂, hA₂⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hLb
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  refine (periodicDeterminant_eq_of_linearEquiv _ _ _ _
    ((0 : Module.End R (singletonQuotient S a)).prodMap eb.toLinearMap)
    (ea.toLinearMap.prodMap (0 : Module.End R (singletonQuotient S b)))
    hex₁ hex₂ e hφ hψ hL hLab).trans ?_
  rw [periodicDeterminant_prodMap 0 ea.toLinearMap h0ea hea0
    eb.toLinearMap 0 heb0 h0eb hLa hLb, periodicDeterminant_zero_equiv,
    periodicDeterminant_equiv_zero]

/-- Multiplication by `b` from the quotient by `a` to the quotient by `ab`. -/
def singletonQuotientMulMap (a b : S) :
    singletonQuotient S a →ₗ[R] singletonQuotient S (a * b) :=
  ((Ideal.span {a}).liftQ
    ((LinearMap.lsmul S (singletonQuotient S (a * b)) b).comp
      (Ideal.span {a * b}).mkQ)
    (by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      change Ideal.Quotient.mk _ (b * (a * y)) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr ⟨y, by ring⟩))).restrictScalars R

/-- `singletonQuotientMulMap a b` sends the class of `x` to the class of `b * x`. -/
theorem singletonQuotientMulMap_mk (a b x : S) :
    singletonQuotientMulMap (R := R) a b (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (b * x) := rfl

/-- Multiplication by a regular element `b` from `S / aS` to `S / abS` is injective. -/
theorem singletonQuotientMulMap_injective (a b : S) (hb : IsRegular b) :
    Function.Injective (singletonQuotientMulMap (R := R) a b) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change singletonQuotientMulMap (R := R) a b (Ideal.Quotient.mk _ x) = 0 →
      Ideal.Quotient.mk _ x = 0
    rw [singletonQuotientMulMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    rintro ⟨y, hy⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr ⟨y, hb.left (by simpa [mul_left_comm, mul_assoc] using hy)⟩)

/-- The quotient by `a` is the image of multiplication by `b` on the quotient by `ab`. -/
noncomputable def singletonQuotientMulRangeEquiv (a b : S) (hb : IsRegular b) :
    singletonQuotient S a ≃ₗ[R] LinearMap.range (singletonQuotientMul R (a * b) b) := by
  let f := singletonQuotientMulMap (R := R) a b
  have hr : f.range = (singletonQuotientMul R (a * b) b).range := by
    ext x
    constructor <;>
    · rintro ⟨y, rfl⟩
      induction y using Submodule.Quotient.induction_on with
      | _ y => exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  exact (LinearEquiv.ofInjective f (singletonQuotientMulMap_injective a b hb)).trans
    (LinearEquiv.ofEq _ _ hr)

/-- `singletonQuotientMulRangeEquiv a b hb` sends the class of `x` to the class of `b * x`. -/
theorem singletonQuotientMulRangeEquiv_mk (a b : S) (hb : IsRegular b) (x : S) :
    ((singletonQuotientMulRangeEquiv (R := R) a b hb (Ideal.Quotient.mk _ x)) :
        singletonQuotient S (a * b)) = Ideal.Quotient.mk _ (b * x) := rfl

/-- The projection from the quotient by `ab` to the quotient by `a`. -/
def singletonQuotientFactor (a b : S) :
    singletonQuotient S (a * b) →ₗ[R] singletonQuotient S a :=
  (Ideal.quotientMapₐ (Ideal.span {a}) (AlgHom.id R S)
    (by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      exact Ideal.mem_span_singleton.mpr ⟨b * y, by simp [mul_assoc]⟩)).toLinearMap

/-- The projection `S / abS → S / aS` sends the class of `x` to the class of `x`. -/
theorem singletonQuotientFactor_mk (a b x : S) :
    singletonQuotientFactor (R := R) a b (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ x := rfl

/-- The projection `S / abS → S / aS` is surjective. -/
theorem singletonQuotientFactor_surjective (a b : S) :
    Function.Surjective (singletonQuotientFactor (R := R) a b) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact ⟨Ideal.Quotient.mk _ x, rfl⟩

/-- For regular `b`, the kernel of the projection `S / abS → S / aS` is the kernel of
multiplication by `b` on `S / abS`. -/
theorem singletonQuotientFactor_ker (a b : S) (hb : IsRegular b) :
    (singletonQuotientFactor (R := R) a b).ker = (singletonQuotientMul R (a * b) b).ker := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change Ideal.Quotient.mk _ x = 0 ↔ Ideal.Quotient.mk _ (b * x) = 0
    simp only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by ring⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hb.left (by simpa [mul_assoc, mul_left_comm] using hy)⟩

/-- The quotient by `a` is the quotient of the quotient by `ab` by the kernel of multiplication
by `b`. -/
noncomputable def singletonQuotientKerMulEquiv (a b : S) (hb : IsRegular b) :
    (singletonQuotient S (a * b) ⧸ (singletonQuotientMul R (a * b) b).ker) ≃ₗ[R]
      singletonQuotient S a :=
  (Submodule.quotEquivOfEq _ _ (singletonQuotientFactor_ker a b hb).symm).trans
    ((singletonQuotientFactor (R := R) a b).quotKerEquivOfSurjective
      (singletonQuotientFactor_surjective a b))

/-- `singletonQuotientKerMulEquiv a b hb` sends the class of the class of `x` to the class of
`x`. -/
theorem singletonQuotientKerMulEquiv_mk (a b : S) (hb : IsRegular b) (x : S) :
    singletonQuotientKerMulEquiv (R := R) a b hb
      (Submodule.Quotient.mk (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ x := rfl

/-- Multiplication by `ab` on `S / dS` is multiplication by `b` followed by multiplication by
`a`. -/
theorem singletonQuotientMul_mul (d a b : S) :
    singletonQuotientMul R d (a * b) =
      singletonQuotientMul R d a ∘ₗ singletonQuotientMul R d b := by
  apply LinearMap.ext
  intro x
  change Ideal.Quotient.mk _ (a * b) * x =
    Ideal.Quotient.mk _ a * (Ideal.Quotient.mk _ b * x)
  rw [map_mul, mul_assoc]

/-- If `ab = d` with `b` regular, then on `S / dS` multiplication by `a` followed by
multiplication by `b` is exact. -/
theorem exact_quotientMul_of_mul_eq (d a b : S) (hab : a * b = d)
    (hb : IsRegular b) :
    Function.Exact (singletonQuotientMul R d a) (singletonQuotientMul R d b) := by
  subst d
  exact exact_singletonQuotientMul a b hb

/-- Three regular elements give three complementary multiplications on the quotient by their
product. -/
theorem singletonQuotientMul_complementary (a b c : S)
    (ha : IsRegular a) (hb : IsRegular b) (hc : IsRegular c) :
    ComplementaryImagesKernels
      (singletonQuotientMul R (a * (b * c)) a)
      (singletonQuotientMul R (a * (b * c)) b)
      (singletonQuotientMul R (a * (b * c)) c) := by
  have hr (x y z : S) (hxyz : x * (y * z) = a * (b * c))
      (hy : IsRegular y) (hz : IsRegular z) :
      (singletonQuotientMul R (a * (b * c)) x).range =
        (singletonQuotientMul R (a * (b * c)) y ∘ₗ singletonQuotientMul R (a * (b * c)) z).ker := by
    rw [← singletonQuotientMul_mul]
    exact (exact_quotientMul_of_mul_eq _ x (y * z) hxyz (hy.mul hz)).linearMap_ker_eq.symm
  have hk (x y z : S) (hxyz : (y * z) * x = a * (b * c)) (hx : IsRegular x) :
      (singletonQuotientMul R (a * (b * c)) x).ker =
        (singletonQuotientMul R (a * (b * c)) y ∘ₗ
          singletonQuotientMul R (a * (b * c)) z).range := by
    rw [← singletonQuotientMul_mul]
    exact (exact_quotientMul_of_mul_eq _ (y * z) x hxyz hx).linearMap_ker_eq
  exact ⟨hr a b c rfl hb hc, hr a c b (by ring) hc hb,
    hr b a c (by ring) ha hc, hr b c a (by ring) hc ha,
    hr c a b (by ring) ha hb, hr c b a (by ring) hb ha,
    hk a b c (by ring) ha, hk a c b (by ring) ha,
    hk b a c (by ring) hb, hk b c a (by ring) hb,
    hk c a b (by ring) hc, hk c b a (by ring) hc⟩

/-- For `ab = d` with `b` regular, the quotient by `a` is the image of multiplication by `b` on the
quotient by `d`. -/
noncomputable def singletonQuotientMulRangeEquivOfEq (d a b : S)
    (hab : a * b = d) (hb : IsRegular b) :
    singletonQuotient S a ≃ₗ[R] LinearMap.range (singletonQuotientMul R d b) := by
  subst d
  exact singletonQuotientMulRangeEquiv a b hb

/-- `singletonQuotientMulRangeEquivOfEq d a b hab hb` sends the class of `x` to the class of
`b * x`. -/
theorem singletonQuotientMulRangeEquivOfEq_mk (d a b : S)
    (hab : a * b = d) (hb : IsRegular b) (x : S) :
    ((singletonQuotientMulRangeEquivOfEq (R := R) d a b hab hb (Ideal.Quotient.mk _ x)) :
        singletonQuotient S d) = Ideal.Quotient.mk _ (b * x) := by
  subst d
  rfl

/-- `singletonQuotientMulRangeEquivOfEq` carries multiplication by `x` on the quotient by `a` to
any endomorphism of the image of multiplication by `b` that acts as multiplication by `x`. -/
theorem singletonQuotientMulRangeEquivOfEq_intertwine (d a b x : S)
    (hab : a * b = d) (hb : IsRegular b)
    (f : LinearMap.range (singletonQuotientMul R d b) →ₗ[R]
      LinearMap.range (singletonQuotientMul R d b))
    (hf : ∀ y, (f y : singletonQuotient S d) = singletonQuotientMul R d x y) :
    (singletonQuotientMulRangeEquivOfEq (R := R) d a b hab hb).toLinearMap.comp
        (singletonQuotientMul R a x) =
      f.comp (singletonQuotientMulRangeEquivOfEq (R := R) d a b hab hb).toLinearMap := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    apply Subtype.ext
    change ((singletonQuotientMulRangeEquivOfEq (R := R) d a b hab hb
      (Ideal.Quotient.mk _ (x * y))) : singletonQuotient S d) = _
    rw [singletonQuotientMulRangeEquivOfEq_mk, LinearMap.comp_apply, hf]
    change Ideal.Quotient.mk _ (b * (x * y)) = singletonQuotientMul R d x
      (singletonQuotientMulRangeEquivOfEq (R := R) d a b hab hb (Ideal.Quotient.mk _ y))
    rw [singletonQuotientMulRangeEquivOfEq_mk]
    change Ideal.Quotient.mk _ (b * (x * y)) =
      Ideal.Quotient.mk _ x * Ideal.Quotient.mk _ (b * y)
    rw [← map_mul, mul_left_comm b x]

/-- For `ab = d` with `b` regular, the quotient by `a` is the quotient of the quotient by `d` by
the kernel of multiplication by `b`. -/
noncomputable def singletonQuotientKerMulEquivOfEq (d a b : S)
    (hab : a * b = d) (hb : IsRegular b) :
    (singletonQuotient S d ⧸ (singletonQuotientMul R d b).ker) ≃ₗ[R] singletonQuotient S a := by
  subst d
  exact singletonQuotientKerMulEquiv a b hb

/-- `singletonQuotientKerMulEquivOfEq d a b hab hb` sends the class of the class of `x` to the
class of `x`. -/
theorem singletonQuotientKerMulEquivOfEq_mk (d a b : S)
    (hab : a * b = d) (hb : IsRegular b) (x : S) :
    singletonQuotientKerMulEquivOfEq (R := R) d a b hab hb
      (Submodule.Quotient.mk (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ x := by
  subst d
  rfl

/-- `singletonQuotientKerMulEquivOfEq` carries any endomorphism of the quotient by the kernel of
multiplication by `b` that acts as multiplication by `x` to multiplication by `x` on the quotient
by `a`. -/
theorem singletonQuotientKerMulEquivOfEq_intertwine (d a b x : S)
    (hab : a * b = d) (hb : IsRegular b)
    (f : (singletonQuotient S d ⧸ (singletonQuotientMul R d b).ker) →ₗ[R]
      (singletonQuotient S d ⧸ (singletonQuotientMul R d b).ker))
    (hf : ∀ y, f (Submodule.Quotient.mk y) = Submodule.Quotient.mk (singletonQuotientMul R d x y)) :
    (singletonQuotientKerMulEquivOfEq (R := R) d a b hab hb).toLinearMap.comp f =
      (singletonQuotientMul R a x).comp
        (singletonQuotientKerMulEquivOfEq (R := R) d a b hab hb).toLinearMap := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf]
      change singletonQuotientKerMulEquivOfEq (R := R) d a b hab hb
        (Submodule.Quotient.mk (Ideal.Quotient.mk _ (x * y))) = _
      rw [singletonQuotientKerMulEquivOfEq_mk]
      change Ideal.Quotient.mk _ (x * y) = singletonQuotientMul R a x
        (singletonQuotientKerMulEquivOfEq (R := R) d a b hab hb
          (Submodule.Quotient.mk (Ideal.Quotient.mk _ y)))
      rw [singletonQuotientKerMulEquivOfEq_mk]
      exact map_mul _ x y

/-- The symbol is multiplicative in its second argument. -/
theorem finiteAlgebraSymbol_mul_right [IsLocalRing R]
    (a b c : S) (ha : IsRegular a) (hb : IsRegular b) (hc : IsRegular c)
    (hL : IsFiniteLength R (singletonQuotient S (a * (b * c))))
    (hLab : IsFiniteLength R (singletonQuotient S (a * b)))
    (hLac : IsFiniteLength R (singletonQuotient S (a * c))) :
    finiteAlgebraSymbol a (b * c) ha (hb.mul hc) hL =
      finiteAlgebraSymbol a b ha hb hLab * finiteAlgebraSymbol a c ha hc hLac := by
  let d := a * (b * c)
  let α := singletonQuotientMul R d a
  let β := singletonQuotientMul R d b
  let γ := singletonQuotientMul R d c
  let h := singletonQuotientMul_complementary (R := R) a b c ha hb hc
  have hmul := periodicDeterminant_mul α β γ hL h
  have habc : (a * b) * c = d := mul_assoc a b c
  have hacb : (a * c) * b = d := (mul_right_comm a c b).trans (mul_assoc a b c)
  have ht₁ := periodicDeterminant_eq_of_linearEquiv
    (singletonQuotientMul R (a * b) a) (singletonQuotientMul R (a * b) b)
    (exact_singletonQuotientMul a b hb) (exact_quotientMul_of_mul_eq _ b a (mul_comm b a) ha)
    (alphaOnGammaRange α β γ h) (betaOnGammaRange α β γ h)
    (exact_alpha_beta_onGammaRange α β γ h)
    (exact_beta_alpha_onGammaRange α β γ h)
    (singletonQuotientMulRangeEquivOfEq d (a * b) c habc hc)
    (singletonQuotientMulRangeEquivOfEq_intertwine d (a * b) c a habc hc _ (fun _ => rfl))
    (singletonQuotientMulRangeEquivOfEq_intertwine d (a * b) c b habc hc _ (fun _ => rfl))
    hLab (hL.of_injective γ.range.subtype_injective)
  have ht₂ := periodicDeterminant_eq_of_linearEquiv
    (alphaOnKerBetaQuotient α β γ h) (gammaOnKerBetaQuotient α β γ h)
    (exact_alpha_gamma_onKerBetaQuotient α β γ h)
    (exact_gamma_alpha_onKerBetaQuotient α β γ h)
    (singletonQuotientMul R (a * c) a) (singletonQuotientMul R (a * c) c)
    (exact_singletonQuotientMul a c hc) (exact_quotientMul_of_mul_eq _ c a (mul_comm c a) ha)
    (singletonQuotientKerMulEquivOfEq d (a * c) b hacb hb)
    (singletonQuotientKerMulEquivOfEq_intertwine d (a * c) b a hacb hb _ (fun _ => rfl))
    (singletonQuotientKerMulEquivOfEq_intertwine d (a * c) b c hacb hb _ (fun _ => rfl))
    (hL.of_surjective (Submodule.mkQ_surjective β.ker)) hLac
  rw [← ht₁, ht₂] at hmul
  simpa only [finiteAlgebraSymbol, singletonQuotientMul_mul] using hmul

/-- The symbol of an element with itself is the sign of the length of the principal quotient. -/
theorem finiteAlgebraSymbol_self [IsLocalRing R]
    (a : S) (ha : IsRegular a)
    (hL : IsFiniteLength R (singletonQuotient S (a * a))) :
    finiteAlgebraSymbol a a ha ha hL =
      (-1 : (IsLocalRing.ResidueField R)ˣ) ^ moduleLength R (singletonQuotient S a) := by
  change periodicDeterminant (singletonQuotientMul R (a * a) a)
    (singletonQuotientMul R (a * a) a) _ _ hL = _
  rw [periodicDeterminant_self_eq_negOne_pow_range_length]
  congr 1
  exact congrArg ENat.toNat (singletonQuotientMulRangeEquiv (R := R) a a ha).length_eq.symm

/-- Interchanging the two arguments inverts the symbol. -/
theorem finiteAlgebraSymbol_swap [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R S]
    (hdim : Module.supportDim R S = 1) (a b : S) (ha : IsRegular a) (hb : IsRegular b)
    (hLab : IsFiniteLength R (singletonQuotient S (a * b)))
    (hLba : IsFiniteLength R (singletonQuotient S (b * a))) :
    finiteAlgebraSymbol a b ha hb hLab * finiteAlgebraSymbol b a hb ha hLba = 1 := by
  have h := endoPeriodicSymbol_swap (LinearMap.mulLeft R a) (LinearMap.mulLeft R b)
    ha.left hb.left (congrArg LinearMap.range (by ext x; simp [mul_left_comm])) hdim
  simpa only [endoPeriodicSymbol_mulLeft hdim a b ha hb,
    endoPeriodicSymbol_mulLeft hdim b a hb ha] using h


/-- The module symbol of two elements of the base ring is the algebra symbol of their images. -/
theorem moduleSymbol_eq_finiteAlgebraSymbol [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R S] (hdim : Module.supportDim R S = 1)
    (a b : R) (ha : IsSMulRegular S a) (hb : IsSMulRegular S b)
    (ha' : IsRegular (algebraMap R S a)) (hb' : IsRegular (algebraMap R S b)) :
    moduleSymbol a b ha hb hdim =
      finiteAlgebraSymbol (algebraMap R S a) (algebraMap R S b) ha' hb'
        (isFiniteLength_singletonQuotient hdim _ (ha'.mul hb')) := by
  rw [← endoPeriodicSymbol_smul]
  have he (x : R) : LinearMap.lsmul R S x = LinearMap.mulLeft R (algebraMap R S x) := by
    ext y
    simp [Algebra.smul_def]
  simpa only [he] using endoPeriodicSymbol_mulLeft hdim _ _ ha' hb'

end AlgebraQuotients

end Stacks.Chow

end
