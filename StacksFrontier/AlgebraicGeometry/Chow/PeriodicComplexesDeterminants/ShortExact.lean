module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.GammaThreeByThree
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Basic

/-!
# Multiplicativity of the periodic determinant in a short exact sequence

The determinant of the middle term of a short exact sequence of exact two-periodic complexes of
finite-length modules over a local ring is the product of the determinants of the two outer
terms.

## Main results

* `AlgebraicGeometry.periodicDeterminant_short_exact` is the multiplicativity formula.

## Implementation notes

A two-periodic complex is given by two endomorphisms. The maps between complexes commute with
both endomorphisms, and their underlying module maps form a short exact sequence. The equations
express these commutative squares as equalities of linear maps.

## References

* [Stacks Project, Tag 02PO](https://stacks.math.columbia.edu/tag/02PO)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

open Module.FiniteLength

namespace AlgebraicGeometry

universe u v₁ v₂ v₃

/-- The map on images induced by a map commuting with the two endomorphisms. -/
private def rangeMap
    {R : Type u} [Semiring R]
    {M : Type v₁} {N : Type v₂}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : M →ₗ[R] N)
    (hcomm : g.comp h = h.comp f) : LinearMap.range f →ₗ[R] LinearMap.range g :=
  LinearMap.codRestrict (LinearMap.range g)
    (h.comp (LinearMap.range f).subtype) (by
      rintro ⟨_, a, rfl⟩
      exact ⟨h a, LinearMap.congr_fun hcomm a⟩)

/-- The induced map on images is injective when the original map is. -/
private theorem rangeMap_injective
    {R : Type u} [Semiring R]
    {M : Type v₁} {N : Type v₂}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : M →ₗ[R] N)
    (hcomm : g.comp h = h.comp f) (hinj : Function.Injective h) :
    Function.Injective (rangeMap f g h hcomm) :=
  fun _ _ hxy => Subtype.ext (hinj (congrArg Subtype.val hxy))

/-- The induced map on images is surjective when the original map is. -/
private theorem rangeMap_surjective
    {R : Type u} [Semiring R]
    {M : Type v₁} {N : Type v₂}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : M →ₗ[R] N)
    (hcomm : g.comp h = h.comp f) (hsurj : Function.Surjective h) :
    Function.Surjective (rangeMap f g h hcomm) := by
  intro y
  obtain ⟨b, hb⟩ := y.2
  obtain ⟨a, rfl⟩ := hsurj b
  exact ⟨⟨f a, a, rfl⟩, Subtype.ext <| (LinearMap.congr_fun hcomm a).symm.trans hb⟩

/-- The induced maps on images of a short exact sequence of periodic complexes are exact. -/
private theorem rangeMap_exact
    {R : Type u} [Semiring R]
    {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f₁ : M₁ →ₗ[R] M₁) (f₂ : M₂ →ₗ[R] M₂) (f₃ : M₃ →ₗ[R] M₃)
    (g₂ : M₂ →ₗ[R] M₂) (g₃ : M₃ →ₗ[R] M₃)
    (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hfi : f₂.comp i = i.comp f₁) (hfp : f₃.comp p = p.comp f₂)
    (hgp : g₃.comp p = p.comp g₂)
    (hgf₂ : Function.Exact g₂ f₂)
    (hgf₃ : Function.Exact g₃ f₃)
    (hsurj : Function.Surjective p)
    (hip : Function.Exact i p) :
    Function.Exact (rangeMap f₁ f₂ i hfi) (rangeMap f₂ f₃ p hfp) := by
  refine LinearMap.exact_iff.mpr (Submodule.ext fun y => ?_)
  change rangeMap f₂ f₃ p hfp y = 0 ↔
    y ∈ LinearMap.range (rangeMap f₁ f₂ i hfi)
  constructor
  · intro hy
    have hyval : p y = 0 := by simpa [rangeMap] using congrArg Subtype.val hy
    obtain ⟨b₀, hb₀⟩ := y.2
    obtain ⟨c, hc⟩ := (hgf₃ (p b₀)).mp <|
      (LinearMap.congr_fun hfp b₀).trans (by simpa [hb₀] using hyval)
    obtain ⟨b₁, hb₁⟩ := hsurj c
    have hgp' : p (g₂ b₁) = g₃ (p b₁) := (LinearMap.congr_fun hgp b₁).symm
    have hker : p (b₀ - g₂ b₁) = 0 := by rw [map_sub, hgp', hb₁, hc, sub_self]
    obtain ⟨a, ha⟩ := (hip (b₀ - g₂ b₁)).mp hker
    have hf : f₂ b₀ = i (f₁ a) := by
      rw [← sub_add_cancel b₀ (g₂ b₁), ← ha, map_add, (hgf₂ (g₂ b₁)).2 ⟨b₁, rfl⟩, add_zero]
      exact LinearMap.congr_fun hfi a
    exact ⟨⟨f₁ a, a, rfl⟩, Subtype.ext (by simpa [rangeMap] using hf.symm.trans hb₀)⟩
  · rintro ⟨⟨_, a, rfl⟩, rfl⟩
    exact Subtype.ext ((hip (i (f₁ a))).2 ⟨f₁ a, rfl⟩)

/-- The induced map on images commutes with the corestrictions to the images. -/
private theorem rangeMap_comp_rangeRestrict
    {R : Type u} [Semiring R]
    {M : Type v₁} {N : Type v₂}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] M) (g : N →ₗ[R] N) (h : M →ₗ[R] N)
    (hcomm : g.comp h = h.comp f) :
    (rangeMap f g h hcomm).comp f.rangeRestrict = g.rangeRestrict.comp h := by
  ext x
  exact (LinearMap.congr_fun hcomm x).symm

/-- The inclusion of the image of `g` is exact with the corestriction of `f` when `g` and `f`
are exact. -/
private theorem exact_subtype_rangeRestrict
    {R : Type u} [Semiring R]
    {M : Type v₁} [AddCommGroup M] [Module R M]
    (f g : M →ₗ[R] M) (h : Function.Exact g f) :
    Function.Exact (LinearMap.range g).subtype f.rangeRestrict := by
  rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  exact h.linearMap_ker_eq

/-- Module length is additive in a short exact sequence of finite-length modules. -/
private theorem moduleLength_eq_add_of_exact
    {R : Type u} [Ring R]
    {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hip : Function.Exact i p)
    (h₁ : IsFiniteLength R M₁) (h₃ : IsFiniteLength R M₃) :
    moduleLength R M₂ = moduleLength R M₁ + moduleLength R M₃ := by
  change (Module.length R M₂).toNat = _
  rw [Module.length_eq_add_of_exact i p hi hp hip,
    ENat.toNat_add (Module.length_ne_top_iff.mpr h₁) (Module.length_ne_top_iff.mpr h₃)]

/-- Interchanging the tensor factors of two signed comparisons multiplies their signs and their
scalars. -/
private theorem periodicGamma_tensor_interchange
    {k : Type u} [CommRing k]
    {A₁ A₃ C₁ C₃ D₁ D₃ : Type*}
    [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₃] [Module k A₃]
    [AddCommGroup C₁] [Module k C₁] [AddCommGroup C₃] [Module k C₃]
    [AddCommGroup D₁] [Module k D₁] [AddCommGroup D₃] [Module k D₃]
    (a₁ a₃ c₁ c₃ : ℕ) (d₁ d₃ : k)
    (α₁ : A₁ ⊗[k] C₁ →ₗ[k] D₁) (α₃ : A₃ ⊗[k] C₃ →ₗ[k] D₃)
    (β₁ : C₁ ⊗[k] A₁ →ₗ[k] D₁) (β₃ : C₃ ⊗[k] A₃ →ₗ[k] D₃)
    (h₁ : β₁.comp (TensorProduct.comm k A₁ C₁).toLinearMap =
      (((-1 : k) ^ (c₁ * a₁) * d₁) • α₁))
    (h₃ : β₃.comp (TensorProduct.comm k A₃ C₃).toLinearMap =
      (((-1 : k) ^ (c₃ * a₃) * d₃) • α₃)) :
    (TensorProduct.map β₁ β₃).comp
        ((signedTensorInterchange k C₁ C₃ A₁ A₃ c₃ a₁).comp
          (TensorProduct.comm k (A₁ ⊗[k] A₃) (C₁ ⊗[k] C₃)).toLinearMap) =
      (((-1 : k) ^ (c₃ * a₁ + c₁ * a₁ + c₃ * a₃ + a₃ * c₁) * d₁ * d₃) •
        ((TensorProduct.map α₁ α₃).comp
          (signedTensorInterchange k A₁ A₃ C₁ C₃ a₃ c₁))) := by
  ext a₁' a₃' c₁' c₃'
  have h₁' : β₁ (c₁' ⊗ₜ[k] a₁') =
      ((-1 : k) ^ (c₁ * a₁) * d₁) • α₁ (a₁' ⊗ₜ[k] c₁') := by
    simpa using LinearMap.congr_fun h₁ (a₁' ⊗ₜ[k] c₁')
  have h₃' : β₃ (c₃' ⊗ₜ[k] a₃') =
      ((-1 : k) ^ (c₃ * a₃) * d₃) • α₃ (a₃' ⊗ₜ[k] c₃') := by
    simpa using LinearMap.congr_fun h₃ (a₃' ⊗ₜ[k] c₃')
  simp only [signedTensorInterchange, TensorProduct.AlgebraTensorModule.curry_apply,
    LinearMap.restrictScalars_self, TensorProduct.curry_apply, LinearMap.coe_comp,
    LinearMap.coe_smul, LinearEquiv.coe_coe, Function.comp_apply, TensorProduct.comm_tmul,
    Pi.smul_apply, LinearEquiv.trans_apply, TensorProduct.assoc_tmul, LinearEquiv.lTensor_tmul,
    TensorProduct.assoc_symm_tmul, LinearEquiv.rTensor_tmul, map_smul, TensorProduct.map_tmul,
    h₁', h₃', TensorProduct.tmul_smul, TensorProduct.smul_tmul, smul_smul, pow_add,
    LinearMap.smul_apply]
  congr 1
  have hcross : (-1 : k) ^ (a₃ * c₁) * (-1) ^ (a₃ * c₁) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc
    _ = ((-1 : k) ^ (c₃ * a₁) * (-1) ^ (c₁ * a₁) *
          (-1) ^ (c₃ * a₃) * d₁ * d₃) := by ring
    _ = ((-1 : k) ^ (c₃ * a₁) * (-1) ^ (c₁ * a₁) *
          (-1) ^ (c₃ * a₃) * d₁ * d₃ *
          ((-1) ^ (a₃ * c₁) * (-1) ^ (a₃ * c₁))) := by
      rw [hcross]
      ring
    _ = ((-1 : k) ^ (c₃ * a₁) * (-1) ^ (c₁ * a₁) *
          (-1) ^ (c₃ * a₃) * (-1) ^ (a₃ * c₁) * d₁ * d₃ *
          (-1) ^ (a₃ * c₁)) := by ring

/-- **Stacks Project, Tag 02PO.** The periodic determinant is multiplicative in a short exact
sequence of exact two-periodic complexes of finite-length modules. -/
@[stacks 02PO]
theorem periodicDeterminant_short_exact
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (φ₁ ψ₁ : M₁ →ₗ[R] M₁) (φ₂ ψ₂ : M₂ →ₗ[R] M₂)
    (φ₃ ψ₃ : M₃ →ₗ[R] M₃)
    (i : M₁ →ₗ[R] M₂) (p : M₂ →ₗ[R] M₃)
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hip : Function.Exact i p)
    (hφi : φ₂.comp i = i.comp φ₁)
    (hψi : ψ₂.comp i = i.comp ψ₁)
    (hφp : φ₃.comp p = p.comp φ₂)
    (hψp : ψ₃.comp p = p.comp ψ₂)
    (hφψ₁ : Function.Exact φ₁ ψ₁) (hψφ₁ : Function.Exact ψ₁ φ₁)
    (hφψ₂ : Function.Exact φ₂ ψ₂) (hψφ₂ : Function.Exact ψ₂ φ₂)
    (hφψ₃ : Function.Exact φ₃ ψ₃) (hψφ₃ : Function.Exact ψ₃ φ₃)
    (hM₁ : IsFiniteLength R M₁) (hM₂ : IsFiniteLength R M₂)
    (hM₃ : IsFiniteLength R M₃) :
    periodicDeterminant φ₂ ψ₂ hφψ₂ hψφ₂ hM₂ =
      periodicDeterminant φ₁ ψ₁ hφψ₁ hψφ₁ hM₁ *
        periodicDeterminant φ₃ ψ₃ hφψ₃ hψφ₃ hM₃ := by
  classical
  let A₁ := LinearMap.range ψ₁
  let A₂ := LinearMap.range ψ₂
  let A₃ := LinearMap.range ψ₃
  let C₁ := LinearMap.range φ₁
  let C₂ := LinearMap.range φ₂
  let C₃ := LinearMap.range φ₃
  let iA := rangeMap ψ₁ ψ₂ i hψi
  let pA := rangeMap ψ₂ ψ₃ p hψp
  let iC := rangeMap φ₁ φ₂ i hφi
  let pC := rangeMap φ₂ φ₃ p hφp
  have hA₁ : IsFiniteLength R A₁ := hM₁.of_injective A₁.subtype_injective
  have hA₂ : IsFiniteLength R A₂ := hM₂.of_injective A₂.subtype_injective
  have hA₃ : IsFiniteLength R A₃ := hM₃.of_injective A₃.subtype_injective
  have hC₁ : IsFiniteLength R C₁ := hM₁.of_injective C₁.subtype_injective
  have hC₂ : IsFiniteLength R C₂ := hM₂.of_injective C₂.subtype_injective
  have hC₃ : IsFiniteLength R C₃ := hM₃.of_injective C₃.subtype_injective
  have hiA : Function.Injective iA := rangeMap_injective ψ₁ ψ₂ i hψi hi
  have hpA : Function.Surjective pA := rangeMap_surjective ψ₂ ψ₃ p hψp hp
  have hiC : Function.Injective iC := rangeMap_injective φ₁ φ₂ i hφi hi
  have hpC : Function.Surjective pC := rangeMap_surjective φ₂ φ₃ p hφp hp
  have hexA : Function.Exact iA pA :=
    rangeMap_exact ψ₁ ψ₂ ψ₃ φ₂ φ₃ i p hψi hψp hφp hφψ₂ hφψ₃ hp hip
  have hexC : Function.Exact iC pC :=
    rangeMap_exact φ₁ φ₂ φ₃ ψ₂ ψ₃ i p hφi hφp hψp hψφ₂ hψφ₃ hp hip
  have hcomm₁ : i.comp A₁.subtype = A₂.subtype.comp iA := by
    ext x
    rfl
  have hcomm₂ : p.comp A₂.subtype = A₃.subtype.comp pA := by
    ext x
    rfl
  have hdiagramφ := determinantExactSequenceMap_three_by_three
    (iAB := iA) (pBC := pA)
    (iDE := i) (pEF := p)
    (iGH := iC) (pHI := pC)
    (iAD := A₁.subtype) (iBE := A₂.subtype) (iCF := A₃.subtype)
    (pDG := φ₁.rangeRestrict) (pEH := φ₂.rangeRestrict) (pFI := φ₃.rangeRestrict)
    hiA hpA hexA hi hp hip hiC hpC hexC
    A₁.subtype_injective φ₁.surjective_rangeRestrict (exact_subtype_rangeRestrict φ₁ ψ₁ hψφ₁)
    A₂.subtype_injective φ₂.surjective_rangeRestrict (exact_subtype_rangeRestrict φ₂ ψ₂ hψφ₂)
    A₃.subtype_injective φ₃.surjective_rangeRestrict (exact_subtype_rangeRestrict φ₃ ψ₃ hψφ₃)
    hcomm₁ hcomm₂ (rangeMap_comp_rangeRestrict φ₁ φ₂ i hφi)
    (rangeMap_comp_rangeRestrict φ₂ φ₃ p hφp)
    hA₁ hA₂ hA₃ hM₁ hM₂ hM₃ hC₁ hC₂ hC₃
  have hdiagramψ := determinantExactSequenceMap_three_by_three
    (iAB := iC) (pBC := pC)
    (iDE := i) (pEF := p)
    (iGH := iA) (pHI := pA)
    (iAD := C₁.subtype) (iBE := C₂.subtype) (iCF := C₃.subtype)
    (pDG := ψ₁.rangeRestrict) (pEH := ψ₂.rangeRestrict) (pFI := ψ₃.rangeRestrict)
    hiC hpC hexC hi hp hip hiA hpA hexA
    C₁.subtype_injective ψ₁.surjective_rangeRestrict (exact_subtype_rangeRestrict ψ₁ φ₁ hφψ₁)
    C₂.subtype_injective ψ₂.surjective_rangeRestrict (exact_subtype_rangeRestrict ψ₂ φ₂ hφψ₂)
    C₃.subtype_injective ψ₃.surjective_rangeRestrict (exact_subtype_rangeRestrict ψ₃ φ₃ hφψ₃)
    (by ext x; rfl) (by ext x; rfl)
    (rangeMap_comp_rangeRestrict ψ₁ ψ₂ i hψi) (rangeMap_comp_rangeRestrict ψ₂ ψ₃ p hψp)
    hC₁ hC₂ hC₃ hM₁ hM₂ hM₃ hA₁ hA₂ hA₃
  let δA := determinantExactSequenceMap iA pA hiA hpA hexA hA₁ hA₂ hA₃
  let δC := determinantExactSequenceMap iC pC hiC hpC hexC hC₁ hC₂ hC₃
  let δM := determinantExactSequenceMap i p hi hp hip hM₁ hM₂ hM₃
  let γφ₁ := periodicGamma φ₁ ψ₁ hψφ₁ hM₁
  let γφ₂ := periodicGamma φ₂ ψ₂ hψφ₂ hM₂
  let γφ₃ := periodicGamma φ₃ ψ₃ hψφ₃ hM₃
  let γψ₁ := periodicGamma ψ₁ φ₁ hφψ₁ hM₁
  let γψ₂ := periodicGamma ψ₂ φ₂ hφψ₂ hM₂
  let γψ₃ := periodicGamma ψ₃ φ₃ hφψ₃ hM₃
  let Sφ := signedTensorInterchange (IsLocalRing.ResidueField R)
    (determinant R A₁) (determinant R A₃) (determinant R C₁) (determinant R C₃)
    (moduleLength R A₃) (moduleLength R C₁)
  let Sψ := signedTensorInterchange (IsLocalRing.ResidueField R)
    (determinant R C₁) (determinant R C₃) (determinant R A₁) (determinant R A₃)
    (moduleLength R C₃) (moduleLength R A₁)
  let E := (TensorProduct.comm (IsLocalRing.ResidueField R)
    (determinant R A₁ ⊗[IsLocalRing.ResidueField R] determinant R A₃)
    (determinant R C₁ ⊗[IsLocalRing.ResidueField R] determinant R C₃)).toLinearMap
  let d₁ := periodicDeterminant φ₁ ψ₁ hφψ₁ hψφ₁ hM₁
  let d₃ := periodicDeterminant φ₃ ψ₃ hφψ₃ hψφ₃ hM₃
  have hlenA := moduleLength_eq_add_of_exact iA pA hiA hpA hexA hA₁ hA₃
  have hlenC := moduleLength_eq_add_of_exact iC pC hiC hpC hexC hC₁ hC₃
  have hspec₁ : γψ₁.comp (TensorProduct.comm (IsLocalRing.ResidueField R)
      (determinant R A₁) (determinant R C₁)).toLinearMap =
      (((-1 : IsLocalRing.ResidueField R) ^
        (moduleLength R C₁ * moduleLength R A₁) *
        (d₁ : IsLocalRing.ResidueField R)) • γφ₁) :=
    periodicDeterminant_spec φ₁ ψ₁ hφψ₁ hψφ₁ hM₁
  have hspec₃ : γψ₃.comp (TensorProduct.comm (IsLocalRing.ResidueField R)
      (determinant R A₃) (determinant R C₃)).toLinearMap =
      (((-1 : IsLocalRing.ResidueField R) ^
        (moduleLength R C₃ * moduleLength R A₃) *
        (d₃ : IsLocalRing.ResidueField R)) • γφ₃) :=
    periodicDeterminant_spec φ₃ ψ₃ hφψ₃ hψφ₃ hM₃
  have hdiagramφ' : γφ₂.comp (TensorProduct.map δA δC) =
      δM.comp ((TensorProduct.map γφ₁ γφ₃).comp Sφ) := hdiagramφ
  have hdiagramψ' : γψ₂.comp (TensorProduct.map δC δA) =
      δM.comp ((TensorProduct.map γψ₁ γψ₃).comp Sψ) := hdiagramψ
  have hinterchange := periodicGamma_tensor_interchange
    (moduleLength R A₁) (moduleLength R A₃)
    (moduleLength R C₁) (moduleLength R C₃)
    (d₁ : IsLocalRing.ResidueField R) (d₃ : IsLocalRing.ResidueField R)
    γφ₁ γφ₃ γψ₁ γψ₃ hspec₁ hspec₃
  have hcommTensor :
      (TensorProduct.comm (IsLocalRing.ResidueField R)
        (determinant R A₂) (determinant R C₂)).toLinearMap.comp
          (TensorProduct.map δA δC) =
        (TensorProduct.map δC δA).comp E := by
    ext a₁ a₃ c₁ c₃
    simp [E]
  let coeff := ((-1 : IsLocalRing.ResidueField R) ^
    (moduleLength R C₃ * moduleLength R A₁ +
      moduleLength R C₁ * moduleLength R A₁ +
      moduleLength R C₃ * moduleLength R A₃ +
      moduleLength R A₃ * moduleLength R C₁) *
      (d₁ : IsLocalRing.ResidueField R) * (d₃ : IsLocalRing.ResidueField R))
  have htransport :
      γψ₂.comp ((TensorProduct.comm (IsLocalRing.ResidueField R)
        (determinant R A₂) (determinant R C₂)).toLinearMap.comp
          (TensorProduct.map δA δC)) =
        coeff • (γφ₂.comp (TensorProduct.map δA δC)) := by
    rw [hcommTensor]
    calc
      γψ₂.comp ((TensorProduct.map δC δA).comp E) =
          (γψ₂.comp (TensorProduct.map δC δA)).comp E := by
            simp [LinearMap.comp_assoc]
      _ = δM.comp ((TensorProduct.map γψ₁ γψ₃).comp (Sψ.comp E)) := by
            simpa [LinearMap.comp_assoc] using
              congrArg (fun f => f.comp E) hdiagramψ'
      _ = δM.comp (coeff • ((TensorProduct.map γφ₁ γφ₃).comp Sφ)) := by
            rw [hinterchange]
      _ = coeff • (δM.comp ((TensorProduct.map γφ₁ γφ₃).comp Sφ)) := by
            ext x
            simp [LinearMap.comp_apply]
      _ = coeff • (γφ₂.comp (TensorProduct.map δA δC)) := by
            rw [← hdiagramφ']
  have hcoeff : coeff =
      ((-1 : IsLocalRing.ResidueField R) ^
        (moduleLength R C₂ * moduleLength R A₂) *
        ((d₁ * d₃ : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)) := by
    dsimp [coeff]
    rw [hlenC, hlenA]
    rw [← mul_assoc]
    congr 1
    ring
  have hδAsurj : Function.Surjective δA :=
    (determinantExactSequenceMap_bijective iA pA hiA hpA hexA hA₁ hA₂ hA₃).2
  have hδCsurj : Function.Surjective δC :=
    (determinantExactSequenceMap_bijective iC pC hiC hpC hexC hC₁ hC₂ hC₃).2
  have hprop : IsPeriodicDeterminant φ₂ ψ₂ hφψ₂ hψφ₂ hM₂ (d₁ * d₃) := by
    change γψ₂.comp (TensorProduct.comm (IsLocalRing.ResidueField R)
      (determinant R A₂) (determinant R C₂)).toLinearMap =
      (((-1 : IsLocalRing.ResidueField R) ^
        (moduleLength R C₂ * moduleLength R A₂) *
        ((d₁ * d₃ : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)) • γφ₂)
    apply LinearMap.ext
    intro x
    obtain ⟨z, hz⟩ := TensorProduct.map_surjective
      (g := δA) (g' := δC) hδAsurj hδCsurj x
    have hval := congrArg (fun f => f z) htransport
    calc
      γψ₂ ((TensorProduct.comm (IsLocalRing.ResidueField R)
          (determinant R A₂) (determinant R C₂)).toLinearMap x) =
        γψ₂ ((TensorProduct.comm (IsLocalRing.ResidueField R)
          (determinant R A₂) (determinant R C₂)).toLinearMap
            (TensorProduct.map δA δC z)) := by rw [← hz]
      _ = coeff • γφ₂ (TensorProduct.map δA δC z) := by
        simpa [LinearMap.comp_apply, LinearMap.smul_apply] using hval
      _ = ((-1 : IsLocalRing.ResidueField R) ^
          (moduleLength R C₂ * moduleLength R A₂) *
          ((d₁ * d₃ : (IsLocalRing.ResidueField R)ˣ) : IsLocalRing.ResidueField R)) •
            γφ₂ x := by rw [hcoeff, hz]
  exact (eq_periodicDeterminant φ₂ ψ₂ hφψ₂ hψφ₂ hM₂ hprop).symm

end AlgebraicGeometry
