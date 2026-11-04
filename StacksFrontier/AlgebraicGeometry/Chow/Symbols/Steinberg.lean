module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.UnitScaling
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Multiplicativity
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.ShortExact
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Sign
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationTameSymbols.Preparation
public import StacksFrontier.AlgebraicGeometry.Chow.Symbols.MinimalPrimes
public import StacksFrontier.RingTheory.LocalRing.PrepareTwoNonZeroDivisors
public import StacksCore.Tactic.StacksAttribute

/-!
# The Steinberg relation for the symbol of a one-dimensional module

Let `A` be a Noetherian local ring and let `M` be a finite `A`-module of support dimension one
on which each of `a`, `b` and `b - a` acts injectively. The four symbols of Tag 02PZ formed from
these elements satisfy

`d_M(a, b - a) * d_M(b, b) = d_M(b, b - a) * d_M(a, b)`

in the units of the residue field of `A`. This is the relation from which the Steinberg relation
for the tame symbol is deduced.

## Main results

* `AlgebraicGeometry.moduleSymbol_steinberg_prepare` is the relation.

## Implementation notes

Nonzerodivisors on the module are expressed by `IsSMulRegular`, and the dimension hypothesis by
`Module.supportDim`.

The proof follows the source. Tag 02Q5 reduces the statement to the quotients `A / q` at the
minimal points of the support of `M`, so that the module is a one-dimensional Noetherian local
ring in its own right, though determinants are still taken over `A`. For elements of a finite
`A`-algebra `S` the relevant symbol is a periodic determinant on `S / abS` taken over `A`; it is
`AlgebraicGeometry.algebraSymbol` here, the `d^A_{A'}` of the source. Multiplicativity, the
inverse relation on swapping the two arguments, and the value on a repeated argument are proved
for it from the corresponding properties of the periodic determinant, Tags 02PU, 02PL and 02PM.

When the two elements are comaximal, the Chinese remainder theorem splits the periodic complex as
a product of two complexes with one differential invertible and the other zero, and Tags 02PN and
02PO evaluate it; multiplication by `b - a` is multiplication by `b` on `S / aS` and by `-a` on
`S / bS`, which produces the sign that the symbol of `b` with itself cancels. In general Tag 02Q7
supplies a finite extension in which the two elements acquire a common factor with comaximal
cofactors, Tag 02Q4 identifies the symbol over the extension with the symbol over the base, and
the comaximal case is transported along the common factor by a formal computation with a
bimultiplicative antisymmetric pairing.

The ring-theoretic input of Tag 02Q7 is
`Stacks.PrepareNonZeroDivisors.finiteExtensionPreparingTwoNonzerodivisors`, which proves the
`Prop`-valued statement `AlgebraicGeometry.FiniteExtensionPreparingTwoNonzerodivisors` for every
one-dimensional Noetherian local ring.

## References

* [Stacks Project, Tag 02Q8](https://stacks.math.columbia.edu/tag/02Q8)
-/

@[expose] public section

open CategoryTheory

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v

/-- The symbol attached to two commuting injective endomorphisms of a finite module of support
dimension one: the periodic determinant of the two-periodic complex they induce on the quotient
by the image of their composite. -/
private noncomputable def endoSymbol
    {A : Type u} {E : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (α β : E →ₗ[A] E) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hcomm : α.comp β = β.comp α) (hdim : Module.supportDim A E = 1) :
    (IsLocalRing.ResidueField A)ˣ :=
  periodicDeterminant
    (periodicQuotientPhi α β (congrArg LinearMap.range hcomm))
    (periodicQuotientPsi α β (congrArg LinearMap.range hcomm))
    (exact_periodicQuotient_phi_psi α β hβ (congrArg LinearMap.range hcomm))
    (exact_periodicQuotient_psi_phi α β hα (congrArg LinearMap.range hcomm))
    (Module.isFiniteLength_quotient_range_of_injective (α.comp β) (hα.comp hβ) hdim)

/-- For multiplications by two ring elements the symbol of the endomorphisms is the module
symbol. -/
private theorem endoSymbol_smul
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hdim : Module.supportDim A M = 1) :
    endoSymbol (LinearMap.lsmul A M a) (LinearMap.lsmul A M b) ha hb
        (by
          ext m
          simp only [LinearMap.comp_apply, LinearMap.lsmul_apply]
          exact smul_comm a b m) hdim =
      moduleSymbol a b ha hb hdim := by
  rfl

/-- Interchanging the two endomorphisms inverts the symbol. -/
private theorem endoSymbol_swap
    {A : Type u} {E : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup E] [Module A E] [Module.Finite A E]
    (α β : E →ₗ[A] E) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hcomm : α.comp β = β.comp α) (hdim : Module.supportDim A E = 1) :
    endoSymbol α β hα hβ hcomm hdim * endoSymbol β α hβ hα hcomm.symm hdim = 1 := by
  let hR := congrArg LinearMap.range hcomm
  let φ := periodicQuotientPhi α β hR
  let ψ := periodicQuotientPsi α β hR
  let φ' := periodicQuotientPhi β α hR.symm
  let ψ' := periodicQuotientPsi β α hR.symm
  let e := Submodule.quotEquivOfEq _ _ hR
  have heφ : e.toLinearMap.comp φ = ψ'.comp e.toLinearMap := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => simp [e, φ, ψ', periodicQuotientPhi, periodicQuotientPsi,
        Submodule.quotEquivOfEq_mk]
  have heψ : e.toLinearMap.comp ψ = φ'.comp e.toLinearMap := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => simp [e, φ', ψ, periodicQuotientPhi, periodicQuotientPsi,
        Submodule.quotEquivOfEq_mk]
  have htrans := periodicDeterminant_eq_of_linearEquiv ψ φ
    (exact_periodicQuotient_psi_phi α β hα hR)
    (exact_periodicQuotient_phi_psi α β hβ hR)
    φ' ψ'
    (exact_periodicQuotient_phi_psi β α hα hR.symm)
    (exact_periodicQuotient_psi_phi β α hβ hR.symm)
    e heψ heφ
    (Module.isFiniteLength_quotient_range_of_injective (α.comp β) (hα.comp hβ) hdim)
    (Module.isFiniteLength_quotient_range_of_injective (β.comp α) (hβ.comp hα) hdim)
  have hswap := periodicDeterminant_mul_swap φ ψ
    (exact_periodicQuotient_phi_psi α β hβ hR)
    (exact_periodicQuotient_psi_phi α β hα hR)
    (Module.isFiniteLength_quotient_range_of_injective (α.comp β) (hα.comp hβ) hdim)
  calc
    endoSymbol α β hα hβ hcomm hdim * endoSymbol β α hβ hα hcomm.symm hdim =
        periodicDeterminant φ ψ
          (exact_periodicQuotient_phi_psi α β hβ hR)
          (exact_periodicQuotient_psi_phi α β hα hR)
          (Module.isFiniteLength_quotient_range_of_injective
            (α.comp β) (hα.comp hβ) hdim) *
        periodicDeterminant φ' ψ'
          (exact_periodicQuotient_phi_psi β α hα hR.symm)
          (exact_periodicQuotient_psi_phi β α hβ hR.symm)
          (Module.isFiniteLength_quotient_range_of_injective
            (β.comp α) (hβ.comp hα) hdim) := by
              simp [endoSymbol, φ, ψ, φ', ψ']
    _ = 1 := by rwa [← htrans]

/-- The product of two exact two-periodic complexes is exact. -/
private theorem exact_prodMap
    {R : Type*} [Ring R] {E₁ E₂ : Type*}
    [AddCommGroup E₁] [Module R E₁] [AddCommGroup E₂] [Module R E₂]
    (φ₁ ψ₁ : E₁ →ₗ[R] E₁) (φ₂ ψ₂ : E₂ →ₗ[R] E₂)
    (h₁ : Function.Exact φ₁ ψ₁) (h₂ : Function.Exact φ₂ ψ₂) :
    Function.Exact (φ₁.prodMap φ₂) (ψ₁.prodMap ψ₂) := by
  intro x
  show (ψ₁ x.1, ψ₂ x.2) = (0, 0) ↔ ∃ y : E₁ × E₂, (φ₁ y.1, φ₂ y.2) = x
  rw [Prod.mk.injEq, h₁, h₂]
  constructor
  · rintro ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩⟩
    exact ⟨(y₁, y₂), Prod.ext hy₁ hy₂⟩
  · rintro ⟨y, hy⟩
    exact ⟨⟨y.1, congrArg Prod.fst hy⟩, ⟨y.2, congrArg Prod.snd hy⟩⟩

/-- A product of two finite-length modules has finite length. -/
private theorem isFiniteLength_prod
    {R : Type*} [Ring R] {E₁ E₂ : Type*}
    [AddCommGroup E₁] [Module R E₁] [AddCommGroup E₂] [Module R E₂]
    (h₁ : IsFiniteLength R E₁) (h₂ : IsFiniteLength R E₂) :
    IsFiniteLength R (E₁ × E₂) := by
  obtain ⟨hN₁, hA₁⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h₁
  obtain ⟨hN₂, hA₂⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h₂
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- The periodic determinant of a product of two exact two-periodic complexes is the product of
their periodic determinants. -/
private theorem periodicDeterminant_prod
    {R : Type u} [CommRing R] [IsLocalRing R]
    {E₁ : Type v} {E₂ : Type*} [AddCommGroup E₁] [Module R E₁]
    [AddCommGroup E₂] [Module R E₂]
    (φ₁ ψ₁ : E₁ →ₗ[R] E₁) (hφ₁ψ₁ : Function.Exact φ₁ ψ₁)
    (hψ₁φ₁ : Function.Exact ψ₁ φ₁)
    (φ₂ ψ₂ : E₂ →ₗ[R] E₂) (hφ₂ψ₂ : Function.Exact φ₂ ψ₂)
    (hψ₂φ₂ : Function.Exact ψ₂ φ₂)
    (hE₁ : IsFiniteLength R E₁) (hE₂ : IsFiniteLength R E₂) :
    periodicDeterminant (φ₁.prodMap φ₂) (ψ₁.prodMap ψ₂)
        (exact_prodMap φ₁ ψ₁ φ₂ ψ₂ hφ₁ψ₁ hφ₂ψ₂)
        (exact_prodMap ψ₁ φ₁ ψ₂ φ₂ hψ₁φ₁ hψ₂φ₂)
        (isFiniteLength_prod hE₁ hE₂) =
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
private abbrev principalQuotient (S : Type*) [CommRing S] (a : S) :=
  S ⧸ Ideal.span ({a} : Set S)

/-- Multiplication by an element on a principal quotient, as a map of modules over the base
ring. -/
private abbrev quotientMul (R : Type*) [CommRing R] {S : Type*} [CommRing S]
    [Algebra R S] (d x : S) : principalQuotient S d →ₗ[R] principalQuotient S d :=
  LinearMap.mulLeft R (Ideal.Quotient.mk _ x)

/-- On `S / abS`, multiplication by `a` followed by multiplication by `b` is exact. -/
private theorem exact_quotientMul (a b : S) (hb : IsRegular b) :
    Function.Exact (quotientMul R (a * b) a) (quotientMul R (a * b) b) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    show (Ideal.Quotient.mk _ b) * (Ideal.Quotient.mk _ x) = 0 ↔ _
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, hy⟩
      have hx : x = a * y := hb.left (by simpa [mul_assoc, mul_left_comm] using hy)
      refine ⟨Ideal.Quotient.mk _ y, ?_⟩
      show (Ideal.Quotient.mk _ a) * (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ x
      rw [← map_mul, hx]
    · rintro ⟨y, hy⟩
      induction y using Submodule.Quotient.induction_on with
      | _ y =>
        change (Ideal.Quotient.mk _ a) * (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ x at hy
        rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
        obtain ⟨z, hz⟩ := hy
        refine ⟨y - b * z, ?_⟩
        linear_combination -b * hz

private theorem exact_quotientMul_of_mul_eq (d a b : S) (hab : a * b = d)
    (hb : IsRegular b) : Function.Exact (quotientMul R d a) (quotientMul R d b) := by
  subst d
  exact exact_quotientMul a b hb

/-- The symbol of two regular elements of a finite algebra, with the determinant taken over the
base ring: the periodic determinant of the two-periodic complex of multiplications they induce
on the quotient by their product. -/
private noncomputable def algebraSymbol [IsLocalRing R]
    (a b : S) (ha : IsRegular a) (hb : IsRegular b)
    (hL : IsFiniteLength R (principalQuotient S (a * b))) :
    (IsLocalRing.ResidueField R)ˣ :=
  periodicDeterminant (quotientMul R (a * b) a) (quotientMul R (a * b) b)
    (exact_quotientMul a b hb)
    (exact_quotientMul_of_mul_eq _ b a (mul_comm b a) ha) hL

/-- The image of multiplication by an element is the ideal it generates. -/
private theorem mulLeft_range (a : S) :
    (LinearMap.mulLeft R a).range = (Ideal.span {a}).restrictScalars R := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mulLeft_apply,
    Submodule.restrictScalars_mem, Ideal.mem_span_singleton]
  exact ⟨fun ⟨y, hy⟩ => ⟨y, hy.symm⟩, fun ⟨y, hy⟩ => ⟨y, hy.symm⟩⟩

/-- The quotient by the image of the composite of two multiplications is the quotient by the
ideal generated by the product. -/
private noncomputable def quotientRangeMulEquiv (a b : S) :
    (S ⧸ (LinearMap.mulLeft R a ∘ₗ LinearMap.mulLeft R b).range) ≃ₗ[R]
      principalQuotient S (a * b) :=
  (Submodule.quotEquivOfEq _ _ (by rw [← LinearMap.mulLeft_mul, mulLeft_range])).trans
    (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {a * b}))

private theorem quotientRangeMulEquiv_mk (a b x : S) :
    quotientRangeMulEquiv (R := R) a b (Submodule.Quotient.mk x) =
      Ideal.Quotient.mk _ x := rfl

/-- For a finite algebra of support dimension one over a Noetherian local ring, the quotient by
a regular element has finite length. -/
private theorem isFiniteLength_principalQuotient [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R S] (hdim : Module.supportDim R S = 1)
    (a : S) (ha : IsRegular a) : IsFiniteLength R (principalQuotient S a) := by
  have h := Module.isFiniteLength_quotient_range_of_injective
    (LinearMap.mulLeft R a) ha.left hdim
  rw [mulLeft_range] at h
  exact (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {a})).isFiniteLength h

/-- The symbol of two multiplications is the symbol of the two elements. -/
private theorem endoSymbol_mulLeft [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R S] (hdim : Module.supportDim R S = 1)
    (a b : S) (ha : IsRegular a) (hb : IsRegular b) :
    endoSymbol (LinearMap.mulLeft R a) (LinearMap.mulLeft R b) ha.left hb.left
        (by ext x; simp [mul_left_comm]) hdim =
      algebraSymbol a b ha hb (isFiniteLength_principalQuotient hdim (a * b) (ha.mul hb)) := by
  apply periodicDeterminant_eq_of_linearEquiv _ _ _ _ _ _ _ _
    (quotientRangeMulEquiv (R := R) a b)
  all_goals
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

private theorem quotientMk_self (a : S) :
    Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton a))

/-- An element coprime to `a` becomes a unit in the quotient by `a`. -/
private theorem isUnit_quotientMk_of_isCoprime (a b : S) (h : IsCoprime a b) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {a}) b) := by
  simpa only [quotientMk_self, isCoprime_zero_left] using h.map (Ideal.Quotient.mk (Ideal.span {a}))

/-- Multiplication by an element coprime to `a` is an automorphism of the quotient by `a`. -/
private noncomputable def quotientMulEquiv (a b : S) (h : IsCoprime a b) :
    principalQuotient S a ≃ₗ[R] principalQuotient S a :=
  (LinearEquiv.smulOfUnit (M := principalQuotient S a)
    (isUnit_quotientMk_of_isCoprime a b h).unit).restrictScalars R

private theorem quotientMulEquiv_apply (a b : S) (h : IsCoprime a b)
    (x : principalQuotient S a) :
    quotientMulEquiv (R := R) a b h x = quotientMul R a b x := by
  simp [quotientMulEquiv, LinearEquiv.smulOfUnit, smul_eq_mul]

/-- The Chinese remainder theorem for two coprime elements. -/
private noncomputable def principalQuotientEquivProd (a b : S) (h : IsCoprime a b) :
    principalQuotient S (a * b) ≃ₐ[R]
      principalQuotient S a × principalQuotient S b := by
  let e := (Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton a b).symm).trans
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {a}) (Ideal.span {b})
      ((Ideal.isCoprime_span_singleton_iff a b).mpr h))
  exact { e with
    commutes' := fun r => by
      apply Prod.ext <;>
        simp [e, Ideal.quotientMulEquivQuotientProd_fst,
          Ideal.quotientMulEquivQuotientProd_snd, ← Ideal.Quotient.mk_algebraMap] }

private theorem principalQuotientEquivProd_mk (a b : S) (h : IsCoprime a b) (x : S) :
    principalQuotientEquivProd (R := R) a b h (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
  apply Prod.ext <;>
    simp [principalQuotientEquivProd, Ideal.quotientMulEquivQuotientProd_fst,
      Ideal.quotientMulEquivQuotientProd_snd]

/-- For two coprime elements the symbol is the ratio of the determinants of the two
multiplication automorphisms on the two principal quotients. -/
private theorem algebraSymbol_of_isCoprime [IsLocalRing R]
    (a b : S) (ha : IsRegular a) (hb : IsRegular b) (h : IsCoprime a b)
    (hL : IsFiniteLength R (principalQuotient S (a * b)))
    (hLa : IsFiniteLength R (principalQuotient S a))
    (hLb : IsFiniteLength R (principalQuotient S b)) :
    algebraSymbol a b ha hb hL =
      (determinantAutomorphism (quotientMulEquiv (R := R) a b h) hLa)⁻¹ *
        determinantAutomorphism (quotientMulEquiv (R := R) b a h.symm) hLb := by
  let ea := quotientMulEquiv (R := R) a b h
  let eb := quotientMulEquiv (R := R) b a h.symm
  let e := (principalQuotientEquivProd (R := R) a b h).toLinearEquiv
  have he_mul (x y : principalQuotient S (a * b)) : e (x * y) = e x * e y :=
    (principalQuotientEquivProd (R := R) a b h).map_mul x y
  have hea : e (Ideal.Quotient.mk _ a) = (0, Ideal.Quotient.mk _ a) := by
    show principalQuotientEquivProd (R := R) a b h (Ideal.Quotient.mk _ a) = _
    rw [principalQuotientEquivProd_mk]
    simp
  have heb : e (Ideal.Quotient.mk _ b) = (Ideal.Quotient.mk _ b, 0) := by
    show principalQuotientEquivProd (R := R) a b h (Ideal.Quotient.mk _ b) = _
    rw [principalQuotientEquivProd_mk]
    simp
  have h0ea : Function.Exact (0 : Module.End R (principalQuotient S a)) ea.toLinearMap :=
    (LinearMap.exact_zero_iff_injective _ _).mpr ea.injective
  have hea0 : Function.Exact ea.toLinearMap (0 : Module.End R (principalQuotient S a)) :=
    (LinearMap.exact_zero_iff_surjective _ _).mpr ea.surjective
  have heb0 : Function.Exact eb.toLinearMap (0 : Module.End R (principalQuotient S b)) :=
    (LinearMap.exact_zero_iff_surjective _ _).mpr eb.surjective
  have h0eb : Function.Exact (0 : Module.End R (principalQuotient S b)) eb.toLinearMap :=
    (LinearMap.exact_zero_iff_injective _ _).mpr eb.injective
  have hφ : e.toLinearMap.comp (quotientMul R (a * b) a) =
      ((0 : Module.End R (principalQuotient S a)).prodMap eb.toLinearMap).comp
        e.toLinearMap := by
    apply LinearMap.ext
    intro x
    dsimp only [LinearMap.comp_apply, quotientMul, LinearMap.mulLeft_apply,
      LinearMap.prodMap_apply, LinearMap.zero_apply, LinearEquiv.coe_coe]
    rw [he_mul, hea]
    simp only [Prod.mul_def, zero_mul]
    rfl
  have hψ : e.toLinearMap.comp (quotientMul R (a * b) b) =
      (ea.toLinearMap.prodMap (0 : Module.End R (principalQuotient S b))).comp
        e.toLinearMap := by
    apply LinearMap.ext
    intro x
    dsimp only [LinearMap.comp_apply, quotientMul, LinearMap.mulLeft_apply,
      LinearMap.prodMap_apply, LinearMap.zero_apply, LinearEquiv.coe_coe]
    rw [he_mul, heb]
    simp only [Prod.mul_def]
    simp [ea, quotientMulEquiv_apply, quotientMul]
  have ht := periodicDeterminant_eq_of_linearEquiv
    (quotientMul R (a * b) a) (quotientMul R (a * b) b)
    (exact_quotientMul a b hb)
    (exact_quotientMul_of_mul_eq _ b a (mul_comm b a) ha)
    ((0 : Module.End R (principalQuotient S a)).prodMap eb.toLinearMap)
    (ea.toLinearMap.prodMap (0 : Module.End R (principalQuotient S b)))
    (exact_prodMap _ _ _ _ h0ea heb0) (exact_prodMap _ _ _ _ hea0 h0eb)
    e hφ hψ
    hL (isFiniteLength_prod hLa hLb)
  rwa [periodicDeterminant_prod 0 ea.toLinearMap h0ea hea0
    eb.toLinearMap 0 heb0 h0eb hLa hLb, periodicDeterminant_zero_equiv,
    periodicDeterminant_equiv_zero] at ht

/-- Multiplication by `b` from the quotient by `a` to the quotient by `ab`. -/
private def quotientMulMap (a b : S) :
    principalQuotient S a →ₗ[R] principalQuotient S (a * b) :=
  ((Ideal.span {a}).liftQ
    ((LinearMap.lsmul S (principalQuotient S (a * b)) b).comp
      (Ideal.span {a * b}).mkQ)
    (by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      change Ideal.Quotient.mk _ (b * (a * y)) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr ⟨y, by ring⟩))).restrictScalars R

private theorem quotientMulMap_mk (a b x : S) :
    quotientMulMap (R := R) a b (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (b * x) := rfl

private theorem quotientMulMap_injective (a b : S) (hb : IsRegular b) :
    Function.Injective (quotientMulMap (R := R) a b) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    show quotientMulMap (R := R) a b (Ideal.Quotient.mk _ x) = 0 →
      Ideal.Quotient.mk _ x = 0
    rw [quotientMulMap_mk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    rintro ⟨y, hy⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton.mpr ⟨y, hb.left (by simpa [mul_left_comm, mul_assoc] using hy)⟩)

/-- The quotient by `a` is the image of multiplication by `b` on the quotient by `ab`. -/
private noncomputable def quotientMulRangeEquiv (a b : S) (hb : IsRegular b) :
    principalQuotient S a ≃ₗ[R] LinearMap.range (quotientMul R (a * b) b) := by
  let f := quotientMulMap (R := R) a b
  have hr : f.range = (quotientMul R (a * b) b).range := by
    ext x
    constructor <;>
    · rintro ⟨y, rfl⟩
      induction y using Submodule.Quotient.induction_on with
      | _ y => exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  exact (LinearEquiv.ofInjective f (quotientMulMap_injective a b hb)).trans
    (LinearEquiv.ofEq _ _ hr)

private theorem quotientMulRangeEquiv_mk (a b : S) (hb : IsRegular b) (x : S) :
    ((quotientMulRangeEquiv (R := R) a b hb (Ideal.Quotient.mk _ x)) :
        principalQuotient S (a * b)) = Ideal.Quotient.mk _ (b * x) := rfl

/-- The projection from the quotient by `ab` to the quotient by `a`. -/
private def principalQuotientFactor (a b : S) :
    principalQuotient S (a * b) →ₗ[R] principalQuotient S a :=
  (Ideal.quotientMapₐ (Ideal.span {a}) (AlgHom.id R S)
    (by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      exact Ideal.mem_span_singleton.mpr ⟨b * y, by simp [mul_assoc]⟩)).toLinearMap

private theorem principalQuotientFactor_mk (a b x : S) :
    principalQuotientFactor (R := R) a b (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ x := rfl

private theorem principalQuotientFactor_surjective (a b : S) :
    Function.Surjective (principalQuotientFactor (R := R) a b) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x => exact ⟨Ideal.Quotient.mk _ x, rfl⟩

private theorem principalQuotientFactor_ker (a b : S) (hb : IsRegular b) :
    (principalQuotientFactor (R := R) a b).ker = (quotientMul R (a * b) b).ker := by
  ext x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    show Ideal.Quotient.mk _ x = 0 ↔ Ideal.Quotient.mk _ (b * x) = 0
    simp only [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, by ring⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hb.left (by simpa [mul_assoc, mul_left_comm] using hy)⟩

/-- The quotient by `a` is the quotient of the quotient by `ab` by the kernel of multiplication
by `b`. -/
private noncomputable def quotientKerMulEquiv (a b : S) (hb : IsRegular b) :
    (principalQuotient S (a * b) ⧸ (quotientMul R (a * b) b).ker) ≃ₗ[R]
      principalQuotient S a :=
  (Submodule.quotEquivOfEq _ _ (principalQuotientFactor_ker a b hb).symm).trans
    ((principalQuotientFactor (R := R) a b).quotKerEquivOfSurjective
      (principalQuotientFactor_surjective a b))

private theorem quotientKerMulEquiv_mk (a b : S) (hb : IsRegular b) (x : S) :
    quotientKerMulEquiv (R := R) a b hb
      (Submodule.Quotient.mk (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ x := rfl

private theorem quotientMul_mul (d a b : S) :
    quotientMul R d (a * b) = quotientMul R d a ∘ₗ quotientMul R d b := by
  apply LinearMap.ext
  intro x
  show Ideal.Quotient.mk _ (a * b) * x =
    Ideal.Quotient.mk _ a * (Ideal.Quotient.mk _ b * x)
  rw [map_mul, mul_assoc]

/-- Three regular elements give three complementary multiplications on the quotient by their
product. -/
private theorem quotientMul_complementary (a b c : S)
    (ha : IsRegular a) (hb : IsRegular b) (hc : IsRegular c) :
    ComplementaryImagesKernels
      (quotientMul R (a * (b * c)) a)
      (quotientMul R (a * (b * c)) b)
      (quotientMul R (a * (b * c)) c) := by
  have hr (x y z : S) (hxyz : x * (y * z) = a * (b * c))
      (hy : IsRegular y) (hz : IsRegular z) :
      (quotientMul R (a * (b * c)) x).range =
        (quotientMul R (a * (b * c)) y ∘ₗ quotientMul R (a * (b * c)) z).ker := by
    rw [← quotientMul_mul]
    exact (exact_quotientMul_of_mul_eq _ x (y * z) hxyz (hy.mul hz)).linearMap_ker_eq.symm
  have hk (x y z : S) (hxyz : (y * z) * x = a * (b * c)) (hx : IsRegular x) :
      (quotientMul R (a * (b * c)) x).ker =
        (quotientMul R (a * (b * c)) y ∘ₗ quotientMul R (a * (b * c)) z).range := by
    rw [← quotientMul_mul]
    exact (exact_quotientMul_of_mul_eq _ (y * z) x hxyz hx).linearMap_ker_eq
  exact ⟨hr a b c rfl hb hc, hr a c b (by ring) hc hb,
    hr b a c (by ring) ha hc, hr b c a (by ring) hc ha,
    hr c a b (by ring) ha hb, hr c b a (by ring) hb ha,
    hk a b c (by ring) ha, hk a c b (by ring) ha,
    hk b a c (by ring) hb, hk b c a (by ring) hb,
    hk c a b (by ring) hc, hk c b a (by ring) hc⟩

private noncomputable def quotientMulRangeEquivOfEq (d a b : S)
    (hab : a * b = d) (hb : IsRegular b) :
    principalQuotient S a ≃ₗ[R] LinearMap.range (quotientMul R d b) := by
  subst d
  exact quotientMulRangeEquiv a b hb

private theorem quotientMulRangeEquivOfEq_mk (d a b : S)
    (hab : a * b = d) (hb : IsRegular b) (x : S) :
    ((quotientMulRangeEquivOfEq (R := R) d a b hab hb (Ideal.Quotient.mk _ x)) :
        principalQuotient S d) = Ideal.Quotient.mk _ (b * x) := by
  subst d
  rfl

private theorem quotientMulRangeEquivOfEq_intertwine (d a b x : S)
    (hab : a * b = d) (hb : IsRegular b)
    (f : LinearMap.range (quotientMul R d b) →ₗ[R] LinearMap.range (quotientMul R d b))
    (hf : ∀ y, (f y : principalQuotient S d) = quotientMul R d x y) :
    (quotientMulRangeEquivOfEq (R := R) d a b hab hb).toLinearMap.comp (quotientMul R a x) =
      f.comp (quotientMulRangeEquivOfEq (R := R) d a b hab hb).toLinearMap := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    apply Subtype.ext
    show ((quotientMulRangeEquivOfEq (R := R) d a b hab hb
      (Ideal.Quotient.mk _ (x * y))) : principalQuotient S d) = _
    rw [quotientMulRangeEquivOfEq_mk, LinearMap.comp_apply, hf]
    show Ideal.Quotient.mk _ (b * (x * y)) = quotientMul R d x
      (quotientMulRangeEquivOfEq (R := R) d a b hab hb (Ideal.Quotient.mk _ y))
    rw [quotientMulRangeEquivOfEq_mk]
    show Ideal.Quotient.mk _ (b * (x * y)) =
      Ideal.Quotient.mk _ x * Ideal.Quotient.mk _ (b * y)
    rw [← map_mul, mul_left_comm b x]

private noncomputable def quotientKerMulEquivOfEq (d a b : S)
    (hab : a * b = d) (hb : IsRegular b) :
    (principalQuotient S d ⧸ (quotientMul R d b).ker) ≃ₗ[R] principalQuotient S a := by
  subst d
  exact quotientKerMulEquiv a b hb

private theorem quotientKerMulEquivOfEq_mk (d a b : S)
    (hab : a * b = d) (hb : IsRegular b) (x : S) :
    quotientKerMulEquivOfEq (R := R) d a b hab hb
      (Submodule.Quotient.mk (Ideal.Quotient.mk _ x)) = Ideal.Quotient.mk _ x := by
  subst d
  rfl

private theorem quotientKerMulEquivOfEq_intertwine (d a b x : S)
    (hab : a * b = d) (hb : IsRegular b)
    (f : (principalQuotient S d ⧸ (quotientMul R d b).ker) →ₗ[R]
      (principalQuotient S d ⧸ (quotientMul R d b).ker))
    (hf : ∀ y, f (Submodule.Quotient.mk y) = Submodule.Quotient.mk (quotientMul R d x y)) :
    (quotientKerMulEquivOfEq (R := R) d a b hab hb).toLinearMap.comp f =
      (quotientMul R a x).comp (quotientKerMulEquivOfEq (R := R) d a b hab hb).toLinearMap := by
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | _ y =>
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hf]
      show quotientKerMulEquivOfEq (R := R) d a b hab hb
        (Submodule.Quotient.mk (Ideal.Quotient.mk _ (x * y))) = _
      rw [quotientKerMulEquivOfEq_mk]
      show Ideal.Quotient.mk _ (x * y) = quotientMul R a x
        (quotientKerMulEquivOfEq (R := R) d a b hab hb
          (Submodule.Quotient.mk (Ideal.Quotient.mk _ y)))
      rw [quotientKerMulEquivOfEq_mk]
      exact map_mul _ x y

/-- The symbol is multiplicative in its second argument. -/
private theorem algebraSymbol_mul_right [IsLocalRing R]
    (a b c : S) (ha : IsRegular a) (hb : IsRegular b) (hc : IsRegular c)
    (hL : IsFiniteLength R (principalQuotient S (a * (b * c))))
    (hLab : IsFiniteLength R (principalQuotient S (a * b)))
    (hLac : IsFiniteLength R (principalQuotient S (a * c))) :
    algebraSymbol a (b * c) ha (hb.mul hc) hL =
      algebraSymbol a b ha hb hLab * algebraSymbol a c ha hc hLac := by
  let d := a * (b * c)
  let α := quotientMul R d a
  let β := quotientMul R d b
  let γ := quotientMul R d c
  let h := quotientMul_complementary (R := R) a b c ha hb hc
  have hmul := periodicDeterminant_mul α β γ hL h
  have habc : (a * b) * c = d := by dsimp [d]; ring
  have hacb : (a * c) * b = d := by dsimp [d]; ring
  have ht₁ := periodicDeterminant_eq_of_linearEquiv
    (quotientMul R (a * b) a) (quotientMul R (a * b) b)
    (exact_quotientMul a b hb) (exact_quotientMul_of_mul_eq _ b a (mul_comm b a) ha)
    (alphaOnGammaRange α β γ h) (betaOnGammaRange α β γ h)
    (exact_alpha_beta_onGammaRange α β γ h)
    (exact_beta_alpha_onGammaRange α β γ h)
    (quotientMulRangeEquivOfEq d (a * b) c habc hc)
    (quotientMulRangeEquivOfEq_intertwine d (a * b) c a habc hc _ (fun _ => rfl))
    (quotientMulRangeEquivOfEq_intertwine d (a * b) c b habc hc _ (fun _ => rfl))
    hLab (hL.of_injective γ.range.subtype_injective)
  have ht₂ := periodicDeterminant_eq_of_linearEquiv
    (alphaOnKerBetaQuotient α β γ h) (gammaOnKerBetaQuotient α β γ h)
    (exact_alpha_gamma_onKerBetaQuotient α β γ h)
    (exact_gamma_alpha_onKerBetaQuotient α β γ h)
    (quotientMul R (a * c) a) (quotientMul R (a * c) c)
    (exact_quotientMul a c hc) (exact_quotientMul_of_mul_eq _ c a (mul_comm c a) ha)
    (quotientKerMulEquivOfEq d (a * c) b hacb hb)
    (quotientKerMulEquivOfEq_intertwine d (a * c) b a hacb hb _ (fun _ => rfl))
    (quotientKerMulEquivOfEq_intertwine d (a * c) b c hacb hb _ (fun _ => rfl))
    (hL.of_surjective (Submodule.mkQ_surjective β.ker)) hLac
  rw [← ht₁, ht₂] at hmul
  simpa only [algebraSymbol, quotientMul_mul] using hmul

/-- The determinant of a composite automorphism is the product of the determinants. -/
private theorem determinantAutomorphism_trans [IsLocalRing R]
    {E : Type*} [AddCommGroup E] [Module R E]
    (e f : E ≃ₗ[R] E) (hE : IsFiniteLength R E) :
    determinantAutomorphism (e.trans f) hE =
      determinantAutomorphism e hE * determinantAutomorphism f hE := by
  show LinearEquiv.det (determinantEquiv (e.trans f) _) =
    LinearEquiv.det (determinantEquiv e _) * LinearEquiv.det (determinantEquiv f _)
  rw [← determinantEquiv_trans e f rfl rfl, LinearEquiv.det_trans]
  exact mul_comm _ _

/-- The determinant of the negation automorphism is the sign of the length. -/
private theorem determinantAutomorphism_neg [IsLocalRing R]
    {E : Type*} [AddCommGroup E] [Module R E] (hE : IsFiniteLength R E) :
    determinantAutomorphism (LinearEquiv.neg R : E ≃ₗ[R] E) hE =
      (-1 : (IsLocalRing.ResidueField R)ˣ) ^ moduleLength R E := by
  let X : FiniteLengthModuleIso R := ⟨⟨ModuleCat.of R E, hE⟩⟩
  let f : X ⟶ X := ⟨CategoryTheory.ObjectProperty.isoMk _ (LinearEquiv.neg R).toModuleIso⟩
  have hd := finrank_determinant_eq_one hE
  have := Module.finite_of_finrank_eq_succ hd
  have hf : ((determinantFunctor R).mapLinearEquiv f).toLinearMap =
      ((-1 : IsLocalRing.ResidueField R) ^ moduleLength R E) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    simpa using determinantFunctor_map_unit_smul X (-1) f (by intro x; simp [f]) x
  apply Units.ext
  unfold determinantAutomorphism
  rw [LinearEquiv.coe_det]
  show LinearMap.det ((determinantFunctor R).mapLinearEquiv f).toLinearMap = _
  rw [hf, LinearMap.det_smul, LinearMap.det_id, hd]
  simp

/-- The symbol of an element with itself is the sign of the length of the principal quotient. -/
private theorem algebraSymbol_self [IsLocalRing R]
    (a : S) (ha : IsRegular a)
    (hL : IsFiniteLength R (principalQuotient S (a * a))) :
    algebraSymbol a a ha ha hL =
      (-1 : (IsLocalRing.ResidueField R)ˣ) ^ moduleLength R (principalQuotient S a) := by
  show periodicDeterminant (quotientMul R (a * a) a)
    (quotientMul R (a * a) a) _ _ hL = _
  rw [periodicDeterminant_self_eq_negOne_pow_range_length]
  congr 1
  exact congrArg ENat.toNat (quotientMulRangeEquiv (R := R) a a ha).length_eq.symm

/-- Interchanging the two arguments inverts the symbol. -/
private theorem algebraSymbol_swap [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R S]
    (hdim : Module.supportDim R S = 1) (a b : S) (ha : IsRegular a) (hb : IsRegular b)
    (hLab : IsFiniteLength R (principalQuotient S (a * b)))
    (hLba : IsFiniteLength R (principalQuotient S (b * a))) :
    algebraSymbol a b ha hb hLab * algebraSymbol b a hb ha hLba = 1 := by
  have h := endoSymbol_swap (LinearMap.mulLeft R a) (LinearMap.mulLeft R b)
    ha.left hb.left (by ext x; simp [mul_left_comm]) hdim
  simpa only [endoSymbol_mulLeft hdim a b ha hb, endoSymbol_mulLeft hdim b a hb ha] using h

/-- A bimultiplicative antisymmetric pairing satisfying the relation on a triple satisfies it on
the triple scaled by a common element. -/
private theorem bilinear_relation_mul_common
    {T G : Type*} [CommMonoid T] [CommGroup G] (D : T → T → G)
    (hmul : ∀ x y z, D x (y * z) = D x y * D x z)
    (hswap : ∀ x y, D x y * D y x = 1)
    (t a b c : T) (h : D a c * D b b = D b c * D a b) :
    D (t * a) (t * c) * D (t * b) (t * b) =
      D (t * b) (t * c) * D (t * a) (t * b) := by
  have hl (x y z : T) : D (x * y) z = D x z * D y z := by
    have h₁ := eq_inv_of_mul_eq_one_left (hswap (x * y) z)
    have h₂ := eq_inv_of_mul_eq_one_left (hswap x z)
    have h₃ := eq_inv_of_mul_eq_one_left (hswap y z)
    rw [h₁, hmul, h₂, h₃, mul_inv]
  simp only [hl, hmul]
  have hb := eq_inv_of_mul_eq_one_left (hswap t b)
  rw [hb]
  calc
    _ = (D t t ^ 2 * D t c * D a t) * (D a c * D b b) := by
      simp [mul_assoc, mul_comm, mul_left_comm, pow_two]
    _ = (D t t ^ 2 * D t c * D a t) * (D b c * D a b) := by rw [h]
    _ = _ := by simp [mul_assoc, mul_comm, mul_left_comm, pow_two]

/-- The relation for two coprime regular elements, by the Chinese remainder theorem. -/
private theorem algebraSymbol_steinberg_of_isCoprime [IsLocalRing R]
    [IsNoetherianRing R] [Module.Finite R S]
    (hdim : Module.supportDim R S = 1)
    (a b : S) (ha : IsRegular a) (hb : IsRegular b) (hba : IsRegular (b - a))
    (h : IsCoprime a b) :
    algebraSymbol a (b - a) ha hba
        (isFiniteLength_principalQuotient hdim _ (ha.mul hba)) *
      algebraSymbol b b hb hb (isFiniteLength_principalQuotient hdim _ (hb.mul hb)) =
    algebraSymbol b (b - a) hb hba
        (isFiniteLength_principalQuotient hdim _ (hb.mul hba)) *
      algebraSymbol a b ha hb (isFiniteLength_principalQuotient hdim _ (ha.mul hb)) := by
  have hac : IsCoprime a (b - a) := by
    simpa using (IsCoprime.sub_mul_left_right_iff (x := a) (y := b) (z := 1)).mpr h
  have hbc : IsCoprime b (b - a) := by
    simpa using (IsCoprime.mul_sub_left_right_iff (x := b) (y := a) (z := 1)).mpr h.symm
  let La := isFiniteLength_principalQuotient hdim a ha
  let Lb := isFiniteLength_principalQuotient hdim b hb
  let Lc := isFiniteLength_principalQuotient hdim (b - a) hba
  rw [algebraSymbol_of_isCoprime a (b - a) ha hba hac _ La Lc,
    algebraSymbol_of_isCoprime b (b - a) hb hba hbc _ Lb Lc,
    algebraSymbol_of_isCoprime a b ha hb h _ La Lb, algebraSymbol_self]
  have he₁ : quotientMulEquiv (R := R) a (b - a) hac = quotientMulEquiv a b h := by
    apply LinearEquiv.ext
    intro x
    simp [quotientMulEquiv_apply]
  have he₂ : quotientMulEquiv (R := R) (b - a) b hbc.symm =
      quotientMulEquiv (b - a) a hac.symm := by
    apply LinearEquiv.ext
    intro x
    simp only [quotientMulEquiv_apply, LinearMap.mulLeft_apply]
    congr 1
    exact Ideal.Quotient.eq.mpr (Ideal.subset_span (Set.mem_singleton _))
  have he₃ : quotientMulEquiv (R := R) b (b - a) hbc =
      (quotientMulEquiv b a h.symm).trans (LinearEquiv.neg R) := by
    apply LinearEquiv.ext
    intro x
    simp [quotientMulEquiv_apply]
  rw [he₁, he₂, he₃, determinantAutomorphism_trans, determinantAutomorphism_neg]
  have hn : ((-1 : (IsLocalRing.ResidueField R)ˣ) ^
      moduleLength R (principalQuotient S b)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm _ 2, pow_mul]
    simp
  have hi : (((-1 : (IsLocalRing.ResidueField R)ˣ) ^
      moduleLength R (principalQuotient S b)))⁻¹ =
      (-1 : (IsLocalRing.ResidueField R)ˣ) ^ moduleLength R (principalQuotient S b) := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using hn
  simp only [mul_inv, hi]
  simp [mul_assoc, mul_comm, mul_left_comm]

/-- The relation for two regular elements with a common factor and coprime cofactors. -/
private theorem algebraSymbol_steinberg_mul_common [IsLocalRing R]
    [IsNoetherianRing R] [Module.Finite R S] (hdim : Module.supportDim R S = 1)
    (t a b : S) (ht : IsRegular t) (ha : IsRegular a) (hb : IsRegular b)
    (hc : IsRegular (b - a)) (hcop : IsCoprime a b) :
    algebraSymbol (t * a) (t * (b - a)) (ht.mul ha) (ht.mul hc)
        (isFiniteLength_principalQuotient hdim _ ((ht.mul ha).mul (ht.mul hc))) *
      algebraSymbol (t * b) (t * b) (ht.mul hb) (ht.mul hb)
        (isFiniteLength_principalQuotient hdim _ ((ht.mul hb).mul (ht.mul hb))) =
    algebraSymbol (t * b) (t * (b - a)) (ht.mul hb) (ht.mul hc)
        (isFiniteLength_principalQuotient hdim _ ((ht.mul hb).mul (ht.mul hc))) *
      algebraSymbol (t * a) (t * b) (ht.mul ha) (ht.mul hb)
        (isFiniteLength_principalQuotient hdim _ ((ht.mul ha).mul (ht.mul hb))) := by
  let D (x y : nonZeroDivisors S) := algebraSymbol (R := R) (x : S) (y : S)
    (isRegular_iff_mem_nonZeroDivisors.mpr x.2) (isRegular_iff_mem_nonZeroDivisors.mpr y.2)
    (isFiniteLength_principalQuotient hdim _ (isRegular_iff_mem_nonZeroDivisors.mpr (x * y).2))
  have hmul (x y z : nonZeroDivisors S) : D x (y * z) = D x y * D x z :=
    algebraSymbol_mul_right _ _ _ _ _ _ _ _ _
  have hswap (x y : nonZeroDivisors S) : D x y * D y x = 1 :=
    algebraSymbol_swap hdim _ _ _ _ _ _
  exact bilinear_relation_mul_common D hmul hswap
    ⟨t, ht.mem_nonZeroDivisors⟩ ⟨a, ha.mem_nonZeroDivisors⟩
    ⟨b, hb.mem_nonZeroDivisors⟩ ⟨b - a, hc.mem_nonZeroDivisors⟩
    (algebraSymbol_steinberg_of_isCoprime hdim a b ha hb hc hcop)

/-- The module symbol of two elements of the base ring is the algebra symbol of their images. -/
private theorem moduleSymbol_eq_algebraSymbol [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R S] (hdim : Module.supportDim R S = 1)
    (a b : R) (ha : IsSMulRegular S a) (hb : IsSMulRegular S b)
    (ha' : IsRegular (algebraMap R S a)) (hb' : IsRegular (algebraMap R S b)) :
    moduleSymbol a b ha hb hdim =
      algebraSymbol (algebraMap R S a) (algebraMap R S b) ha' hb'
        (isFiniteLength_principalQuotient hdim _ (ha'.mul hb')) := by
  rw [← endoSymbol_smul]
  have he (x : R) : LinearMap.lsmul R S x = LinearMap.mulLeft R (algebraMap R S x) := by
    ext y
    simp [Algebra.smul_def]
  simpa only [he] using endoSymbol_mulLeft hdim _ _ ha' hb'

/-- An element acting injectively on an algebra has regular image. -/
private theorem regular_algebraMap_of_smulRegular (a : R) (ha : IsSMulRegular S a) :
    IsRegular (algebraMap R S a) := by
  have hl : IsLeftRegular (algebraMap R S a) := by
    simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def] using ha
  exact ⟨hl, by simpa only [IsRightRegular, IsLeftRegular, mul_comm] using hl⟩

/-- A finite-length module has support dimension at most zero. -/
private theorem supportDim_le_zero_of_finiteLength [IsLocalRing R]
    {E : Type*} [AddCommGroup E] [Module R E] [Module.Finite R E]
    (hE : IsFiniteLength R E) : Module.supportDim R E ≤ 0 := by
  nontriviality E
  rw [Module.supportDim, support_of_isFiniteLength hE]
  exact Order.krullDim_nonpos_of_subsingleton

/-- An injective algebra map between two finite algebras does not change the support
dimension. -/
private theorem supportDim_algebra_eq_of_injective
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Module.Finite A B] [Module.Finite A C]
    (hi : Function.Injective (algebraMap B C)) :
    Module.supportDim A C = Module.supportDim A B := by
  have he : Module.annihilator A C = Module.annihilator A B := by
    ext a
    simp only [Module.mem_annihilator]
    constructor
    · intro h b
      apply hi
      simpa only [Algebra.smul_def, map_mul, map_zero,
        IsScalarTower.algebraMap_apply A B C] using h (algebraMap B C b)
    · intro h c
      have h1 := h 1
      rw [Algebra.smul_def, mul_one] at h1
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B C, h1, map_zero, zero_mul]
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator,
    Module.supportDim_eq_ringKrullDim_quotient_annihilator, he]

/-- If a power of a regular element carries the extension into the base, then regular elements of
the base stay regular in the extension. -/
private theorem regular_algebraMap_of_range_pow
    {B C : Type*} [CommRing B] [CommRing C] [Algebra B C]
    (hi : Function.Injective (algebraMap B C)) (u : B)
    (hu : IsRegular (algebraMap B C u)) (n : ℕ)
    (hn : ∀ z : C, ∃ r : B, algebraMap B C r = algebraMap B C (u ^ n) * z)
    (c : B) (hc : IsRegular c) : IsRegular (algebraMap B C c) := by
  have hzero (z : C) (hz : algebraMap B C c * z = 0) : z = 0 := by
    obtain ⟨r, hr⟩ := hn z
    have hr0 : r = 0 := hc.left (by
      apply hi
      show algebraMap B C (c * r) = algebraMap B C (c * 0)
      rw [mul_zero, map_mul, hr, map_zero]
      calc
        _ = algebraMap B C (u ^ n) * (algebraMap B C c * z) := by ring
        _ = 0 := by rw [hz, mul_zero])
    apply (hu.pow n).left
    simpa [map_pow, hr0] using hr.symm
  exact isRegular_iff_mem_nonZeroDivisors.mpr
    (mem_nonZeroDivisors_iff.mpr ⟨hzero, fun z hz => hzero z (by simpa [mul_comm] using hz)⟩)

/-- If a power of a regular element carries the extension into the base, then the quotient of the
extension by the base has finite length. -/
private theorem finiteLength_coker_of_range_pow
    {A B C : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C]
    [IsScalarTower A B C] [Module.Finite A C]
    (hdim : Module.supportDim A C = 1) (a : A) (ha : IsSMulRegular C a) (n : ℕ)
    (hn : ∀ z : C, ∃ r : B, algebraMap B C r = (a ^ n) • z) :
    IsFiniteLength A (C ⧸ ((Algebra.linearMap B C).restrictScalars A).range) := by
  let α := (Algebra.linearMap B C).restrictScalars A
  let f := LinearMap.lsmul A C (a ^ n)
  have hp : f.range ≤ α.range := by
    rintro _ ⟨z, rfl⟩
    exact hn z
  let p := f.range.mapQ α.range (LinearMap.id : C →ₗ[A] C) hp
  have hsurj : Function.Surjective p := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  exact (Module.isFiniteLength_quotient_range_of_injective
    f (IsSMulRegular.pow n ha) hdim).of_surjective hsurj

end AlgebraQuotients

/-- The relation for a finite algebra which is a one-dimensional Noetherian local ring. The
preparation of two nonzerodivisors of Tag 02Q7 is taken as an argument so that the shape matches
the tame-symbol preparation that consumes the same `Prop`;
`Stacks.PrepareNonZeroDivisors.finiteExtensionPreparingTwoNonzerodivisors` supplies it. -/
private theorem moduleSymbol_steinberg_of_finite_algebra
    (h02Q7 : FiniteExtensionPreparingTwoNonzerodivisors.{u})
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    [Algebra A B] [Module.Finite A B]
    (hdim : Module.supportDim A B = 1) (hdB : ringKrullDim B = 1)
    (a b : A) (ha : IsSMulRegular B a) (hb : IsSMulRegular B b)
    (hc : IsSMulRegular B (b - a)) :
    moduleSymbol a (b - a) ha hc hdim * moduleSymbol b b hb hb hdim =
      moduleSymbol b (b - a) hb hc hdim * moduleSymbol a b ha hb hdim := by
  let aB := algebraMap A B a
  let bB := algebraMap A B b
  have ra : IsRegular aB := regular_algebraMap_of_smulRegular a ha
  have rb : IsRegular bB := regular_algebraMap_of_smulRegular b hb
  have rc : IsRegular (bB - aB) := by
    simpa only [map_sub] using regular_algebraMap_of_smulRegular (b - a) hc
  have convertSymbol (x y : A) (hx : IsSMulRegular B x) (hy : IsSMulRegular B y) :=
    moduleSymbol_eq_algebraSymbol hdim x y hx hy
      (regular_algebraMap_of_smulRegular x hx) (regular_algebraMap_of_smulRegular y hy)
  by_cases hcop : IsCoprime aB bB
  · rw [convertSymbol a (b - a) ha hc, convertSymbol b b hb hb,
      convertSymbol b (b - a) hb hc, convertSymbol a b ha hb]
    simpa only [map_sub] using algebraSymbol_steinberg_of_isCoprime hdim aB bB ra rb rc hcop
  have ham : aB ∈ IsLocalRing.maximalIdeal B := by
    intro hu
    apply hcop
    obtain ⟨u, hu⟩ := hu
    rw [← hu]
    exact ⟨↑u⁻¹, 0, by simp⟩
  obtain ⟨S, hSring, hBS, hfin, hi, ⟨n, hn⟩, t, a', b', ht, ha', hb', hfa, hfb, hspan⟩ :=
    h02Q7 B hdB aB bB ra.mem_nonZeroDivisors rb.mem_nonZeroDivisors
  let _ : CommRing S := hSring
  let _ : Algebra B S := hBS
  let _ : Module.Finite B S := hfin
  let _ : Algebra A S := ((algebraMap B S).comp (algebraMap A B)).toAlgebra
  let _ : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Module.Finite A S := Module.Finite.trans B S
  have hdS : Module.supportDim A S = 1 := (supportDim_algebra_eq_of_injective hi).trans hdim
  have rt : IsRegular t := isRegular_iff_mem_nonZeroDivisors.mpr ht
  have ra' : IsRegular a' := isRegular_iff_mem_nonZeroDivisors.mpr ha'
  have rb' : IsRegular b' := isRegular_iff_mem_nonZeroDivisors.mpr hb'
  have ras : IsRegular (algebraMap B S aB) := hfa.symm ▸ rt.mul ra'
  have hp (z : S) : ∃ r : B, algebraMap B S r = algebraMap B S (aB ^ n) * z := by
    have hzero := Module.mem_annihilator.mp (hn (Ideal.pow_mem_pow ham n))
      (Submodule.Quotient.mk z)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hzero
    obtain ⟨r, hr⟩ := hzero
    exact ⟨r, by simpa only [Algebra.smul_def, Algebra.linearMap_apply] using hr⟩
  have reg (x : A) (hx : IsSMulRegular B x) : IsRegular (algebraMap A S x) :=
    regular_algebraMap_of_range_pow hi aB ras n hp (algebraMap A B x)
      (regular_algebraMap_of_smulRegular x hx)
  have smreg (x : A) (hx : IsSMulRegular B x) : IsSMulRegular S x := (reg x hx).left
  let α := (Algebra.linearMap B S).restrictScalars A
  have hker : Module.supportDim A α.ker ≤ 0 := by
    have he : α.ker = ⊥ := LinearMap.ker_eq_bot.mpr hi
    rw [he, Module.supportDim_eq_bot_of_subsingleton]
    exact bot_le
  have hL : IsFiniteLength A (S ⧸ α.range) :=
    finiteLength_coker_of_range_pow hdS a (smreg a ha) n (by
      simpa only [Algebra.smul_def, map_pow, IsScalarTower.algebraMap_apply A B S] using hp)
  have hcomp (x y : A) (hx : IsSMulRegular B x) (hy : IsSMulRegular B y) :=
    moduleSymbol_eq_of_ker_coker_supportDim_le_zero α x y hx hy
      (smreg x hx) (smreg y hy) hdim hdS hker (supportDim_le_zero_of_finiteLength hL)
  rw [hcomp a (b - a) ha hc, hcomp b b hb hb,
    hcomp b (b - a) hb hc, hcomp a b ha hb]
  have conv (x y : A) (hx : IsSMulRegular B x) (hy : IsSMulRegular B y) :=
    moduleSymbol_eq_algebraSymbol hdS x y (smreg x hx) (smreg y hy) (reg x hx) (reg y hy)
  rw [conv a (b - a) ha hc, conv b b hb hb, conv b (b - a) hb hc, conv a b ha hb]
  have haS : algebraMap A S a = t * a' := hfa
  have hbS : algebraMap A S b = t * b' := hfb
  have hcS : algebraMap A S (b - a) = t * (b' - a') := by rw [map_sub, hbS, haS, mul_sub]
  have rc' : IsRegular (b' - a') := (hcS ▸ reg (b - a) hc).of_mul_right
  have hcop' : IsCoprime a' b' := by
    rw [← Ideal.isCoprime_span_singleton_iff, Ideal.isCoprime_iff_sup_eq]
    simpa only [← Ideal.span_union, Set.singleton_union] using hspan
  simpa only [haS, hbS, hcS] using
    algebraSymbol_steinberg_mul_common hdS t a' b' rt ra' rb' rc' hcop'

/-- **Stacks Project, Tag 02Q8.** Let `A` be a Noetherian local ring, let `a b : A`, and let `M`
be a finite `A`-module of support dimension one on which each of `a`, `b` and `b - a` acts
injectively. Then

`d_M(a, b - a) * d_M(b, b) = d_M(b, b - a) * d_M(a, b)`

in the units of the residue field of `A`. -/
@[stacks 02Q8]
theorem moduleSymbol_steinberg_prepare
    {A : Type u} {M : Type v} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (a b : A) (ha : IsSMulRegular M a) (hb : IsSMulRegular M b)
    (hba : IsSMulRegular M (b - a))
    (hdim : Module.supportDim A M = 1) :
    moduleSymbol a (b - a) ha hba hdim * moduleSymbol b b hb hb hdim =
      moduleSymbol b (b - a) hb hba hdim * moduleSymbol a b ha hb hdim := by
  classical
  have : Finite {q : PrimeSpectrum A // Minimal (· ∈ Module.support A M) q} :=
    finite_minimal_support.to_subtype
  let _ := Fintype.ofFinite {q : PrimeSpectrum A // Minimal (· ∈ Module.support A M) q}
  obtain ⟨ha₁, hc₁, hd₁, h₁⟩ :=
    moduleSymbol_eq_finprod_minimal_support a (b - a) ha hba hdim
  obtain ⟨hb₂, hb₂', hd₂, h₂⟩ :=
    moduleSymbol_eq_finprod_minimal_support b b hb hb hdim
  obtain ⟨hb₃, hc₃, hd₃, h₃⟩ :=
    moduleSymbol_eq_finprod_minimal_support b (b - a) hb hba hdim
  obtain ⟨ha₄, hb₄, hd₄, h₄⟩ :=
    moduleSymbol_eq_finprod_minimal_support a b ha hb hdim
  rw [h₁, h₂, h₃, h₄]
  simp only [finprod_eq_prod_of_fintype, ← Finset.prod_mul_distrib, ← mul_pow]
  apply Finset.prod_congr rfl
  intro q _
  have : q.1.asIdeal.IsPrime := q.1.isPrime
  have : IsLocalRing (A ⧸ q.1.asIdeal) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have hdB : ringKrullDim (A ⧸ q.1.asIdeal) = 1 := by
    simpa only [Module.supportDim_quotient_eq_ringKrullDim] using hd₁ q
  exact congrArg (fun z => z ^
    (Module.length (Localization.AtPrime q.1.asIdeal)
      (LocalizedModule q.1.asIdeal.primeCompl M)).toNat)
    (moduleSymbol_steinberg_of_finite_algebra
      Stacks.PrepareNonZeroDivisors.finiteExtensionPreparingTwoNonzerodivisors
      (hd₁ q) hdB a b (ha₁ q) (hb₂ q) (hc₁ q))

end AlgebraicGeometry
