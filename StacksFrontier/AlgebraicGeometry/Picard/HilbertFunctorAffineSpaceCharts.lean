module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMapDegree
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorOpenSubfunctor
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorSupportedInOpen
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorRepresentableLocal
public import Mathlib.AlgebraicGeometry.AffineSpace
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field

/-!
# The charts `F_W` of the Hilbert functor of an affine space

Let `S` be a scheme, `n` an index type and `d` a natural number, and let
`W_1, …, W_d ∈ Γ(S, 𝒪_S)[x_i ; i ∈ n]`. In the proof of Stacks Tag 0B99 the degree-`d` Hilbert
functor of `𝔸(n; S)` is covered by the subfunctors `F_W`: a family `Z ⊂ 𝔸(n; T)` lies in
`F_W(T)` when the map `𝒪_T^d ⟶ (Z ⟶ T)_* 𝒪_Z`, `e_l ↦ W_l|_Z`, is surjective. This file
constructs these subfunctors and proves that they are open and that, over an affine base, they
cover the field-valued points; these are conditions (2)(b) and (2)(c) of the gluing criterion of
Stacks 01JJ as the proof of Stacks 0B99 uses it.

## Main definitions

* `Stacks.Hilbert.IsChart`: the chart condition on global sections, that the `W_l|_Z` generate
  `Γ(Z, 𝒪_Z)` over `Γ(T, 𝒪_T)`.
* `Stacks.Hilbert.chartSubfunctor`: the subfunctor `F_W`.
* `Stacks.Hilbert.chartLocus`: the open subset of `T` over which a family lies in `F_W`.

## Main results

* `Stacks.Hilbert.IsChart.baseChange`: the chart condition is stable under base change between
  affine schemes.
* `Stacks.Hilbert.isChart_baseChange_iff`: over an affine base the chart condition at a
  field-valued point is read off the support of the cokernel of the chart map (Nakayama).
* `Stacks.Hilbert.isOpenHilbertSubfunctor_chartSubfunctor`: `F_W` is an open subfunctor.
* `Stacks.Hilbert.exists_mem_chartSubfunctor_of_specField`: over an affine base every family
  over a field lies in some `F_W`, with the `W_l` monomials.

## Implementation notes

*The condition defining `F_W`.* Surjectivity of a map from a free module onto a finite module
is a fibrewise condition by Nakayama's lemma, so `F_W(T)` is defined as the set of families
whose base change to every affine scheme with a field of global functions satisfies the chart
condition `Stacks.Hilbert.IsChart` on global sections. Stability under base change is then
immediate, and over an affine `T` the condition is equivalent to the chart condition on `T`
itself (`Stacks.Hilbert.isChart_of_mem_chartSubfunctor`).

*Fibres.* For `T` affine and a field-valued point `T'' ⟶ T` with kernel `p ⊆ Γ(T, 𝒪_T)`, the
global sections of the base changed family are `K ⊗ Γ(Z, 𝒪_Z)`, because the cartesian square of
affine schemes is a pushout square of rings (`AlgebraicGeometry.isPushout_appTop_of_isPullback`).
Right exactness of the tensor product and Nakayama's lemma for the finite cokernel `C` of the
chart map then show that the chart condition holds at the point exactly when `p ∉ Supp C`. Since
`Supp C` is closed, the chart locus is open. This is the argument of Stacks 00O0 for the
surjectivity locus.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 00O0](https://stacks.math.columbia.edu/tag/00O0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Hilbert

/-! ### Sections of a pushout of rings -/

/-- In a pushout square of commutative rings every element of the pushout is a finite sum of
products of an element coming from one side with an element coming from the other. -/
theorem mem_closure_of_isPushout {A B C D : CommRingCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {inl : B ⟶ D} {inr : C ⟶ D} (h : IsPushout f g inl inr) (x : D) :
    x ∈ AddSubmonoid.closure (Set.range fun p : C × B ↦ inr p.1 * inl p.2) := by
  algebraize [f.hom, g.hom, inl.hom, inr.hom, inl.hom.comp f.hom]
  have : IsScalarTower A C D := .of_algebraMap_eq fun a ↦ by
    have e := congr($(h.w).hom a)
    exact e
  have hP : Algebra.IsPushout A B C D := (CommRingCat.isPushout_iff_isPushout.mp h.flip).symm
  obtain ⟨y, rfl⟩ := (Algebra.IsPushout.equiv A B C D).surjective x
  induction y with
  | tmul b c =>
    rw [Algebra.IsPushout.equiv_tmul, mul_comm]
    exact AddSubmonoid.subset_closure ⟨(c, b), rfl⟩
  | add y z hy hz => simpa using AddSubmonoid.add_mem _ hy hz

/-! ### Polynomial functions and the chart condition -/

/-- The affine space `𝔸(n; S)` as a scheme over `S`. -/
abbrev affineSpaceOver (S : Scheme.{u}) (n : Type u) : Over S :=
  Over.mk (𝔸(n; S) ↘ S)

/-- A polynomial with coefficients in `Γ(S, ⊤)` as a global function on `𝔸(n; S)`: the
coefficients are pulled back along the structure morphism and the variables are the
coordinates. -/
def polyFun (S : Scheme.{u}) (n : Type u) : MvPolynomial n Γ(S, ⊤) →+* Γ(𝔸(n; S), ⊤) :=
  MvPolynomial.eval₂Hom (𝔸(n; S) ↘ S).appTop.hom (AffineSpace.coord S)

variable {S : Scheme.{u}} {n : Type u} {d : ℕ}

/-- The map `Γ(T, 𝒪_T)^d ⟶ Γ(Z, 𝒪_Z)` sending `c` to `∑ c_l · W_l|_Z`, for a family `Z` in the
affine space over `T`. -/
def chartMap {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) (c : Fin d → Γ(T.left, ⊤)) :
    Γ(Z.ideal.subscheme, ⊤) :=
  ∑ l, Z.structural.appTop (c l) * Z.toAmbient.appTop (polyFun S n (W l))

/-- The *chart condition* on global sections: the functions `W_l|_Z` generate the global
sections of `Z` over the global sections of `T`. Over an affine base this is the surjectivity
of `𝒪_T^d ⟶ (Z ⟶ T)_* 𝒪_Z`, `e_l ↦ W_l|_Z`. -/
def IsChart {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) : Prop :=
  Function.Surjective (chartMap Z W)

/-- The chart map is additive. -/
@[simp]
theorem chartMap_add {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) (c c' : Fin d → Γ(T.left, ⊤)) :
    chartMap Z W (c + c') = chartMap Z W c + chartMap Z W c' := by
  simp [chartMap, add_mul, Finset.sum_add_distrib]

/-- The chart map sends zero to zero. -/
@[simp]
theorem chartMap_zero {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) : chartMap Z W 0 = 0 := by
  simp [chartMap]

/-- The structure morphisms of a family and of its base change are compatible on global
sections. -/
theorem baseChangeMap_appTop_structural {T' T : Over S} (g : T' ⟶ T)
    (Z : HilbertFamily (affineSpaceOver S n) T d) (x : Γ(T.left, ⊤)) :
    (Z.baseChangeMap g).appTop (Z.structural.appTop x) =
      (baseChange _ g Z).structural.appTop (g.left.appTop x) := by
  have e := congrArg (fun φ ↦ φ.appTop.hom x) (Z.isPullback_baseChangeMap g).w
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using e

/-- The ambient projections of a family and of its base change are compatible on global
sections. -/
theorem baseChangeMap_appTop_toAmbient {T' T : Over S} (g : T' ⟶ T)
    (Z : HilbertFamily (affineSpaceOver S n) T d) (x : Γ(𝔸(n; S), ⊤)) :
    (Z.baseChangeMap g).appTop (Z.toAmbient.appTop x) =
      (baseChange _ g Z).toAmbient.appTop x := by
  rw [HilbertFamily.baseChange_toAmbient]
  rfl

/-- The chart map commutes with base change. -/
theorem baseChangeMap_appTop_chartMap {T' T : Over S} (g : T' ⟶ T)
    (Z : HilbertFamily (affineSpaceOver S n) T d) (W : Fin d → MvPolynomial n Γ(S, ⊤))
    (c : Fin d → Γ(T.left, ⊤)) :
    (Z.baseChangeMap g).appTop (chartMap Z W c) =
      chartMap (baseChange _ g Z) W (fun l ↦ g.left.appTop (c l)) := by
  simp only [chartMap, map_sum, map_mul, baseChangeMap_appTop_structural,
    baseChangeMap_appTop_toAmbient]

/-- **Base change preserves the chart condition** over affine bases. -/
theorem IsChart.baseChange {T' T : Over S} [IsAffine T.left] [IsAffine T'.left] (g : T' ⟶ T)
    {Z : HilbertFamily (affineSpaceOver S n) T d} {W : Fin d → MvPolynomial n Γ(S, ⊤)}
    (hZ : IsChart Z W) : IsChart (baseChange _ g Z) W := by
  have : IsAffine Z.ideal.subscheme := isAffine_of_isAffineHom Z.structural
  have hpo := isPushout_appTop_of_isPullback (Z.isPullback_baseChangeMap g)
  intro y
  induction mem_closure_of_isPushout hpo y using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨c, b⟩, rfl⟩ := hx
    obtain ⟨cb, rfl⟩ := hZ b
    refine ⟨fun l ↦ c * g.left.appTop (cb l), ?_⟩
    change _ = _ * _
    rw [baseChangeMap_appTop_chartMap]
    simp only [chartMap, Finset.mul_sum, map_mul, mul_assoc]
  | zero => exact ⟨0, chartMap_zero _ _⟩
  | add x y _ _ hx hy =>
    obtain ⟨cx, rfl⟩ := hx
    obtain ⟨cy, rfl⟩ := hy
    exact ⟨cx + cy, chartMap_add _ _ _ _⟩

/-! ### Fibres of a cokernel and its support -/

open TensorProduct

section Fibre

variable {A C K : Type*} [CommRing A] [AddCommGroup C] [Module A C] [CommRing K] [Algebra A K]

/-- The prime ideal of `A` which is the kernel of a map to a field. -/
def kerPrime (A K : Type*) [CommRing A] [CommRing K] [Algebra A K] (hK : IsField K) :
    PrimeSpectrum A :=
  ⟨RingHom.ker (algebraMap A K), by
    let := hK.toField
    exact RingHom.ker_isPrime _⟩

/-- Let `C` be a finite module over `A` and `A ⟶ K` a map to a field with kernel `p`. Then `p`
lies outside the support of `C` exactly when the base change `K ⊗_A C` vanishes. One direction
is Nakayama's lemma on the fibre `κ(p) ⊗_A C`, base changed along the field extension
`κ(p) ⟶ K`; the other kills `K ⊗_A C` by an element of the annihilator outside `p`. -/
theorem notMem_support_iff_subsingleton_tensorProduct [Module.Finite A C] (hK : IsField K) :
    kerPrime A K hK ∉ Module.support A C ↔ Subsingleton (K ⊗[A] C) := by
  set p := kerPrime A K hK
  have : p.asIdeal.IsPrime := p.isPrime
  have hunit (a : A) (ha : a ∉ p.asIdeal) : IsUnit (algebraMap A K a) := by
    obtain ⟨b, hb⟩ := hK.mul_inv_cancel (show algebraMap A K a ≠ 0 from ha)
    exact .of_mul_eq_one _ hb
  constructor
  · intro hp
    rw [Module.mem_support_iff_of_finite, IsConcreteLE.not_le_iff_exists] at hp
    obtain ⟨a, ha, hap⟩ := hp
    obtain ⟨u, hu⟩ := hunit a hap
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    induction x with
    | add x y hx hy => rw [hx, hy, add_zero]
    | tmul k c =>
      calc k ⊗ₜ[A] c = (a • (k * ↑u⁻¹)) ⊗ₜ[A] c := by
            rw [Algebra.smul_def, ← hu, mul_left_comm, Units.mul_inv, mul_one]
        _ = (k * ↑u⁻¹) ⊗ₜ[A] (a • c) := TensorProduct.smul_tmul _ _ _
        _ = 0 := by rw [Module.mem_annihilator.mp ha c, TensorProduct.tmul_zero]
  · intro h hp
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
    let ι : p.asIdeal.ResidueField →+* K :=
      Ideal.ResidueField.lift p.asIdeal (algebraMap A K) le_rfl fun x hx ↦ hunit x hx
    let := ι.toAlgebra
    have : IsScalarTower A p.asIdeal.ResidueField K := .of_algebraMap_eq fun x ↦
      (Ideal.ResidueField.lift_algebraMap _ _ _ _ x).symm
    have : Nontrivial K := ⟨hK.exists_pair_ne⟩
    have e := AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField K K C
    have h₁ : Nontrivial (K ⊗[p.asIdeal.ResidueField] (p.asIdeal.ResidueField ⊗[A] C)) :=
      (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right _ _).mpr hp
    exact not_nontrivial_iff_subsingleton.mpr h (e.nontrivial_congr.mp h₁)

end Fibre

section Span

variable {A C K : Type*} [CommRing A] [AddCommGroup C] [Module A C] [CommRing K] [Algebra A K]
  {ι : Type*}

/-- Base change of the cokernel of a family `w` of elements vanishes exactly when the images
`1 ⊗ w_i` span the base change: tensor product is right exact. -/
theorem subsingleton_tensorProduct_quotient_iff (w : ι → C) :
    Subsingleton (K ⊗[A] (C ⧸ Submodule.span A (Set.range w))) ↔
      Submodule.span K (Set.range (TensorProduct.mk A K C 1 ∘ w)) = ⊤ := by
  set N := Submodule.span A (Set.range w)
  have hspan : N.baseChange K = Submodule.span K (Set.range (TensorProduct.mk A K C 1 ∘ w)) := by
    rw [Submodule.baseChange_span, ← Set.range_comp]
  have hex : Function.Exact (LinearMap.lTensor K N.subtype) (LinearMap.lTensor K N.mkQ) :=
    lTensor_exact K (LinearMap.exact_subtype_mkQ N) N.mkQ_surjective
  have hsurj : Function.Surjective (LinearMap.lTensor K N.mkQ) :=
    LinearMap.lTensor_surjective K N.mkQ_surjective
  rw [← hspan]
  constructor
  · intro hsub
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy⟩ := (hex x).mp (Subsingleton.elim _ _)
    exact ⟨y, hy⟩
  · intro htop
    refine subsingleton_of_forall_eq 0 fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨z, rfl⟩ : x ∈ N.baseChange K := htop ▸ Submodule.mem_top
    exact hex.apply_apply_eq_zero z

/-- Spanning after base change does not depend on the model of the base change: two maps
`C ⟶ D`, `C ⟶ D'` exhibiting `D` and `D'` as base changes of `C` to `K` send a family to
spanning families simultaneously. -/
theorem span_range_eq_top_iff_of_isBaseChange {D D' : Type*} [AddCommGroup D] [Module A D]
    [Module K D] [IsScalarTower A K D] [AddCommGroup D'] [Module A D'] [Module K D']
    [IsScalarTower A K D'] {h : C →ₗ[A] D} {h' : C →ₗ[A] D'} (hh : IsBaseChange K h)
    (hh' : IsBaseChange K h') (w : ι → C) :
    Submodule.span K (Set.range (h ∘ w)) = ⊤ ↔ Submodule.span K (Set.range (h' ∘ w)) = ⊤ := by
  let e : D ≃ₗ[K] D' := hh.equiv.symm.trans hh'.equiv
  have he (c : C) : e (h c) = h' c := by
    have h₁ : hh.equiv ((1 : K) ⊗ₜ c) = h c := by rw [hh.equiv_tmul, one_smul]
    simp only [e, LinearEquiv.trans_apply, ← h₁, LinearEquiv.symm_apply_apply,
      hh'.equiv_tmul, one_smul]
  have hr : Set.range (h' ∘ w) = e '' Set.range (h ∘ w) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun i ↦ (he (w i)).symm)
  rw [hr, Submodule.span_image_linearEquiv, Submodule.map_eq_top_iff]

end Span

/-! ### The chart condition at a field-valued point -/

/-- For a family `Z` over `T`, the support in `Spec Γ(T, 𝒪_T)` of the cokernel of the chart map
`Γ(T, 𝒪_T)^d ⟶ Γ(Z, 𝒪_Z)`. -/
def cokernelSupport {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) : Set (PrimeSpectrum Γ(T.left, ⊤)) :=
  letI := Z.structural.appTop.hom.toAlgebra
  Module.support Γ(T.left, ⊤) (Γ(Z.ideal.subscheme, ⊤) ⧸ Submodule.span Γ(T.left, ⊤)
    (Set.range fun l ↦ Z.toAmbient.appTop (polyFun S n (W l))))

/-- The point of `Spec Γ(T, 𝒪_T)` under a morphism from an affine scheme whose ring of global
functions is a field: the kernel of the map on global sections. -/
def fieldPointPrime {T T'' : Over S} (h : T'' ⟶ T) (hK : IsField Γ(T''.left, ⊤)) :
    PrimeSpectrum Γ(T.left, ⊤) :=
  letI := h.left.appTop.hom.toAlgebra
  kerPrime Γ(T.left, ⊤) Γ(T''.left, ⊤) hK

/-- For a family of elements of an algebra, generating it as a module is the surjectivity of
the associated linear combination map, written with the algebra map. -/
theorem surjective_sum_algebraMap_mul_iff {K M : Type*} [CommRing K] [CommRing M] [Algebra K M]
    {ι : Type*} [Fintype ι] (v : ι → M) :
    Function.Surjective (fun c : ι → K ↦ ∑ l, algebraMap K M (c l) * v l) ↔
      Submodule.span K (Set.range v) = ⊤ := by
  rw [span_range_eq_top_iff_surjective_fintypeLinearCombination]
  refine Iff.of_eq (congrArg Function.Surjective (funext fun c ↦ ?_))
  simp [Fintype.linearCombination_apply, Algebra.smul_def]

/-- **The chart condition at a field-valued point.** Let `Z` be a family over an affine `T` and
let `h : T'' ⟶ T` be a morphism from an affine scheme whose global functions form a field `K`,
with kernel `p ⊆ Γ(T, 𝒪_T)`. The base change of `Z` along `h` satisfies the chart condition
exactly when `p` is not in the support of the cokernel of the chart map of `Z`. -/
theorem isChart_baseChange_iff {T T'' : Over S} [IsAffine T.left] [IsAffine T''.left]
    (h : T'' ⟶ T) (hK : IsField Γ(T''.left, ⊤)) (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) :
    IsChart (baseChange _ h Z) W ↔ fieldPointPrime h hK ∉ cokernelSupport Z W := by
  have : IsAffine Z.ideal.subscheme := isAffine_of_isAffineHom Z.structural
  have hpo := isPushout_appTop_of_isPullback (Z.isPullback_baseChangeMap h)
  set Z'' := baseChange _ h Z
  set w : Fin d → Γ(Z.ideal.subscheme, ⊤) := fun l ↦ Z.toAmbient.appTop (polyFun S n (W l))
  have hfin := Z.structural.finite_appTop
  algebraize [Z.structural.appTop.hom, h.left.appTop.hom, (Z.baseChangeMap h).appTop.hom,
    Z''.structural.appTop.hom, (Z.baseChangeMap h).appTop.hom.comp Z.structural.appTop.hom]
  have : IsScalarTower Γ(T.left, ⊤) Γ(T''.left, ⊤) Γ(Z''.ideal.subscheme, ⊤) :=
    .of_algebraMap_eq fun a ↦ by
      have e := congr($(hpo.w).hom a)
      exact e
  have hP : Algebra.IsPushout Γ(T.left, ⊤) Γ(T''.left, ⊤) Γ(Z.ideal.subscheme, ⊤)
      Γ(Z''.ideal.subscheme, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp hpo.flip
  have hbc : IsBaseChange Γ(T''.left, ⊤)
      (IsScalarTower.toAlgHom Γ(T.left, ⊤) Γ(Z.ideal.subscheme, ⊤)
        Γ(Z''.ideal.subscheme, ⊤)).toLinearMap := hP.out
  have hchart : IsChart Z'' W ↔ Submodule.span Γ(T''.left, ⊤)
      (Set.range ((IsScalarTower.toAlgHom Γ(T.left, ⊤) Γ(Z.ideal.subscheme, ⊤)
        Γ(Z''.ideal.subscheme, ⊤)).toLinearMap ∘ w)) = ⊤ := by
    rw [← surjective_sum_algebraMap_mul_iff]
    refine Iff.of_eq (congrArg Function.Surjective (funext fun c ↦ ?_))
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    exact congrArg (_ * ·) (baseChangeMap_appTop_toAmbient h Z _).symm
  rw [hchart, span_range_eq_top_iff_of_isBaseChange hbc (TensorProduct.isBaseChange _ _ _),
    ← subsingleton_tensorProduct_quotient_iff, cokernelSupport, fieldPointPrime,
    notMem_support_iff_subsingleton_tensorProduct hK]

/-! ### Field-valued points -/

/-- A scheme which is affine with a field of global functions has exactly one point, seen in
`Spec Γ(T'', 𝒪)` as the zero ideal. -/
theorem toSpecΓ_apply_asIdeal_eq_bot {T'' : Scheme.{u}} (hK : IsField Γ(T'', ⊤)) (x : T'') :
    (T''.toSpecΓ x).asIdeal = ⊥ := by
  let := hK.toField
  have := (T''.toSpecΓ x : PrimeSpectrum Γ(T'', ⊤)).isPrime
  exact Ideal.eq_bot_of_prime _

/-- A scheme which is affine with a field of global functions is nonempty. -/
theorem nonempty_of_isField {T'' : Scheme.{u}} [IsAffine T''] (hK : IsField Γ(T'', ⊤)) :
    Nonempty T'' := by
  have : Nontrivial Γ(T'', ⊤) := ⟨hK.exists_pair_ne⟩
  exact ⟨T''.isoSpec.inv (Classical.arbitrary (PrimeSpectrum Γ(T'', ⊤)))⟩

/-- A scheme which is affine with a field of global functions has at most one point. -/
theorem subsingleton_of_isField {T'' : Scheme.{u}} [IsAffine T''] (hK : IsField Γ(T'', ⊤)) :
    Subsingleton T'' := by
  refine ⟨fun x y ↦ ?_⟩
  have hinj : Function.Injective T''.isoSpec.hom :=
    (ConcreteCategory.bijective_of_isIso T''.isoSpec.hom.base).1
  refine hinj (PrimeSpectrum.ext ?_)
  rw [Scheme.isoSpec_hom, toSpecΓ_apply_asIdeal_eq_bot hK, toSpecΓ_apply_asIdeal_eq_bot hK]

/-- The image of the point of a field-valued test scheme `h : T'' ⟶ T` in `Spec Γ(T, 𝒪_T)` is
the kernel of the map on global sections. -/
theorem toSpecΓ_apply_eq_fieldPointPrime {T T'' : Over S} (h : T'' ⟶ T)
    (hK : IsField Γ(T''.left, ⊤)) (x : T''.left) :
    T.left.toSpecΓ (h.left x) = fieldPointPrime h hK := by
  rw [← Scheme.Hom.comp_apply, Scheme.toSpecΓ_naturality, Scheme.Hom.comp_apply, Spec.map_apply]
  refine PrimeSpectrum.ext ?_
  change Ideal.comap h.left.appTop.hom (T''.left.toSpecΓ x).asIdeal = RingHom.ker _
  rw [toSpecΓ_apply_asIdeal_eq_bot hK, ← RingHom.ker_eq_comap_bot]
  rfl

/-- The spectrum of a residue field is affine. -/
instance (T : Over S) (t : T.left) : IsAffine (residueFieldOver T t).left :=
  inferInstanceAs (IsAffine (Spec _))

/-- The global functions on the spectrum of a field form a field. -/
private theorem isField_Γ_spec (K : Type u) [Field K] : IsField Γ(Spec (.of K), ⊤) :=
  MulEquiv.isField (Field.toIsField K)
    (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv

/-- The global functions on the spectrum of a residue field form a field. -/
theorem isField_residueFieldOver (T : Over S) (t : T.left) :
    IsField Γ((residueFieldOver T t).left, ⊤) :=
  isField_Γ_spec (T.left.residueField t)

/-- The spectrum of the residue field of `t` has a point over `t`. -/
private theorem exists_residueFieldOver_point (T : Over S) (t : T.left) :
    ∃ x : (residueFieldOver T t).left, (residueFieldOverHom T t).left x = t :=
  ⟨(nonempty_of_isField (isField_residueFieldOver T t)).some,
    Scheme.fromSpecResidueField_apply _ _⟩

/-! ### The locus where a family is a chart -/

/-- An affine open of `T`, as a scheme over `S`, is affine. -/
theorem isAffine_openOver {T : Over S} {V : T.left.Opens} (hV : IsAffineOpen V) :
    IsAffine (Over.restrict T V).left :=
  hV

/-- The support of the cokernel of the chart map over an affine base is closed. -/
theorem isClosed_cokernelSupport {T : Over S} [IsAffine T.left]
    (Z : HilbertFamily (affineSpaceOver S n) T d) (W : Fin d → MvPolynomial n Γ(S, ⊤)) :
    IsClosed (cokernelSupport Z W) := by
  let := Z.structural.appTop.hom.toAlgebra
  have : Module.Finite Γ(T.left, ⊤) Γ(Z.ideal.subscheme, ⊤) := Z.structural.finite_appTop
  rw [cokernelSupport, Module.support_eq_zeroLocus]
  exact PrimeSpectrum.isClosed_zeroLocus _

/-- **The chart condition at a field-valued point, read on an affine open.** If a field-valued
point `h : T'' ⟶ T` hits a point `y` of an affine open `V ⊆ T`, then the base change of `Z` along
`h` satisfies the chart condition exactly when `y` is outside the support of the cokernel of the
chart map of `Z|_V`. -/
theorem isChart_baseChange_iff_of_mem {T T'' : Over S} (V : T.left.Opens) (hV : IsAffineOpen V)
    (h : T'' ⟶ T) [IsAffine T''.left] (hK : IsField Γ(T''.left, ⊤))
    (Z : HilbertFamily (affineSpaceOver S n) T d) (W : Fin d → MvPolynomial n Γ(S, ⊤))
    (y : V) (x : T''.left) (hx : h.left x = V.ι y) :
    IsChart (baseChange _ h Z) W ↔
      (V : Scheme).toSpecΓ y ∉ cokernelSupport (baseChange _ (Over.restrictι T V) Z) W := by
  have : IsAffine V := hV
  have := isAffine_openOver (T := T) hV
  have := subsingleton_of_isField hK
  have hsub : Set.range h.left ⊆ Set.range V.ι := by
    rintro _ ⟨x', rfl⟩
    rw [Subsingleton.elim x' x, hx]
    exact ⟨y, rfl⟩
  set h' : T''.left ⟶ V := IsOpenImmersion.lift V.ι h.left hsub
  have hfac : h' ≫ V.ι = h.left := IsOpenImmersion.lift_fac _ _ _
  let h'' : T'' ⟶ Over.restrict T V := Over.homMk h' (by
    change h' ≫ (V.ι ≫ T.hom) = _
    rw [← Category.assoc, hfac, Over.w h])
  have hh : h = h'' ≫ Over.restrictι T V := by
    ext1
    exact hfac.symm
  have hy : h' x = y := V.ι.isOpenEmbedding.injective (by
    rw [← Scheme.Hom.comp_apply, hfac, hx])
  rw [hh, baseChange_comp, isChart_baseChange_iff h'' hK,
    ← toSpecΓ_apply_eq_fieldPointPrime h'' hK x]
  change (V : Scheme).toSpecΓ (h' x) ∉ _ ↔ _
  rw [hy]

/-- The locus of points `t ∈ T` over which the family `Z` is a chart: every field-valued point
of `T` hitting `t` pulls `Z` back to a family satisfying the chart condition. -/
def chartLocus {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) : Set T.left :=
  {t | ∀ (T'' : Over S) (h : T'' ⟶ T), IsAffine T''.left → IsField Γ(T''.left, ⊤) →
    t ∈ Set.range h.left → IsChart (baseChange _ h Z) W}

/-- Membership in the chart locus, read on an affine open. -/
theorem mem_chartLocus_iff_of_mem {T : Over S} (V : T.left.Opens) (hV : IsAffineOpen V)
    (Z : HilbertFamily (affineSpaceOver S n) T d) (W : Fin d → MvPolynomial n Γ(S, ⊤))
    (y : V) :
    V.ι y ∈ chartLocus Z W ↔
      (V : Scheme).toSpecΓ y ∉ cokernelSupport (baseChange _ (Over.restrictι T V) Z) W := by
  rw [chartLocus, Set.mem_ofPred_eq]
  constructor
  · intro hy
    have hK := isField_residueFieldOver T (V.ι y)
    obtain ⟨x, hx⟩ := exists_residueFieldOver_point T (V.ι y)
    exact (isChart_baseChange_iff_of_mem V hV _ hK Z W y x hx).mp
      (hy _ _ inferInstance hK ⟨x, hx⟩)
  · rintro hy T'' h _ hK ⟨x, hx⟩
    exact (isChart_baseChange_iff_of_mem V hV h hK Z W y x hx).mpr hy

/-- The chart locus of a family is open. -/
theorem isOpen_chartLocus {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (W : Fin d → MvPolynomial n Γ(S, ⊤)) : IsOpen (chartLocus Z W) := by
  rw [isOpen_iff_forall_mem_open]
  intro t ht
  obtain ⟨V, hV, htV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show t ∈ (⊤ : T.left.Opens) from trivial)
  have : IsAffine V := hV
  have := isAffine_openOver (T := T) hV
  refine ⟨V.ι '' ((V : Scheme).toSpecΓ ⁻¹'
    (cokernelSupport (baseChange _ (Over.restrictι T V) Z) W)ᶜ), ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_chartLocus_iff_of_mem V hV Z W y).mpr hy
  · exact V.ι.isOpenEmbedding.isOpenMap _
      (((isClosed_cokernelSupport _ W).isOpen_compl).preimage (V : Scheme).toSpecΓ.continuous)
  · obtain ⟨y, rfl⟩ : t ∈ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
    exact ⟨y, (mem_chartLocus_iff_of_mem V hV Z W y).mp ht, rfl⟩

/-- Two field-valued points through the same point of `T` see the chart condition alike. -/
theorem isChart_baseChange_of_isChart_baseChange {T T₁ T₂ : Over S}
    (Z : HilbertFamily (affineSpaceOver S n) T d) (W : Fin d → MvPolynomial n Γ(S, ⊤))
    (h₁ : T₁ ⟶ T) (h₂ : T₂ ⟶ T) [IsAffine T₁.left] [IsAffine T₂.left]
    (hK₁ : IsField Γ(T₁.left, ⊤)) (hK₂ : IsField Γ(T₂.left, ⊤)) (x₁ : T₁.left) (x₂ : T₂.left)
    (hx : h₁.left x₁ = h₂.left x₂) (h : IsChart (baseChange _ h₁ Z) W) :
    IsChart (baseChange _ h₂ Z) W := by
  obtain ⟨V, hV, htV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show h₁.left x₁ ∈ (⊤ : T.left.Opens) from trivial)
  obtain ⟨y, hy⟩ : h₁.left x₁ ∈ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
  rw [isChart_baseChange_iff_of_mem V hV h₂ hK₂ Z W y x₂ (hx ▸ hy.symm)]
  exact (isChart_baseChange_iff_of_mem V hV h₁ hK₁ Z W y x₁ hy.symm).mp h

/-! ### The subfunctors `F_W` and their openness -/

variable (S n d) in
/-- **The subfunctor `F_W` of the Hilbert functor of `𝔸(n; S)`** attached to `d` polynomials
`W_1, …, W_d`: a family `Z` over `T` lies in `F_W(T)` when the map
`𝒪_T^d ⟶ (Z ⟶ T)_* 𝒪_Z`, `e_l ↦ W_l|_Z`, is surjective. Surjectivity of a map from a free
module onto a finite one is checked on fibres by Nakayama's lemma, so the condition is phrased
on field-valued points: the base change of `Z` to every affine scheme with a field of global
functions satisfies the chart condition. This makes the subfunctor property, stability under
base change, immediate. -/
def chartSubfunctor (W : Fin d → MvPolynomial n Γ(S, ⊤)) :
    Subfunctor (hilbertFunctorOfRank (affineSpaceOver S n) d) where
  obj T := {Z : HilbertFamily (affineSpaceOver S n) T.unop d | ∀ (T'' : Over S)
    (h : T'' ⟶ T.unop), IsAffine T''.left → IsField Γ(T''.left, ⊤) →
      IsChart (baseChange (affineSpaceOver S n) h Z) W}
  map {T T'} g Z hZ T'' h haff hK := by
    have key : baseChange (affineSpaceOver S n) (h ≫ g.unop)
        (Z : HilbertFamily (affineSpaceOver S n) T.unop d) =
          baseChange (affineSpaceOver S n) h (baseChange (affineSpaceOver S n) g.unop Z) :=
      baseChange_comp _ _ _ _
    change IsChart (baseChange (affineSpaceOver S n) h
      (baseChange (affineSpaceOver S n) g.unop (Z : HilbertFamily _ T.unop d))) W
    rw [← key]
    exact hZ T'' (h ≫ g.unop) haff hK

/-- Membership in `F_W(T)`: every field-valued point pulls the family back to a chart. -/
theorem mem_chartSubfunctor_iff {W : Fin d → MvPolynomial n Γ(S, ⊤)} {T : Over S}
    {Z : HilbertFamily (affineSpaceOver S n) T d} :
    Z ∈ (chartSubfunctor S n d W).obj (Opposite.op T) ↔
      ∀ (T'' : Over S) (h : T'' ⟶ T), IsAffine T''.left →
        IsField Γ(T''.left, ⊤) → IsChart (baseChange _ h Z) W :=
  Iff.rfl

/-- **Openness of `F_W`** (condition (2)(b) of Stacks 01JJ in the proof of Stacks 0B99): for a
family `Z` over `T`, the base change along `g : T' ⟶ T` lies in `F_W` exactly when `g` maps
into the open chart locus of `Z`. -/
theorem isOpenHilbertSubfunctor_chartSubfunctor (W : Fin d → MvPolynomial n Γ(S, ⊤)) :
    IsOpenHilbertSubfunctor (chartSubfunctor S n d W) := by
  intro T Z
  refine ⟨⟨chartLocus Z W, isOpen_chartLocus Z W⟩, fun T' g ↦ ?_⟩
  rw [mem_chartSubfunctor_iff]
  constructor
  · rintro hZ _ ⟨t', rfl⟩
    change ∀ (T'' : Over S) (h : T'' ⟶ T), IsAffine T''.left → ∀ hK : IsField Γ(T''.left, ⊤),
      g.left t' ∈ Set.range h.left → IsChart (baseChange _ h Z) W
    rintro T'' h _ hK ⟨x, hx⟩
    have hK₀ := isField_residueFieldOver T' t'
    obtain ⟨x₀, hx₀⟩ := exists_residueFieldOver_point T' t'
    have h₀ := hZ _ (residueFieldOverHom T' t') inferInstance hK₀
    rw [← baseChange_comp] at h₀
    refine isChart_baseChange_of_isChart_baseChange Z W _ h hK₀ hK x₀ x ?_ h₀
    rw [hx, Over.comp_left, Scheme.Hom.comp_apply, hx₀]
  · intro hsub T'' h _ hK
    obtain ⟨x⟩ := nonempty_of_isField hK
    rw [← baseChange_comp]
    exact hsub ⟨h.left x, rfl⟩ T'' (h ≫ g) inferInstance hK ⟨x, rfl⟩

/-! ### Monomials span the sections of a family -/

/-- Over an affine base, every global function on `𝔸(n; S)` is a polynomial in the
coordinates. -/
theorem polyFun_surjective (S : Scheme.{u}) [IsAffine S] (n : Type u) :
    Function.Surjective (polyFun S n) := by
  intro y
  have hy := congrArg (fun φ ↦ φ.appTop.hom y) (AffineSpace.isoOfIsAffine n S).hom_inv_id
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] at hy
  refine ⟨(Scheme.ΓSpecIso _).hom ((AffineSpace.isoOfIsAffine n S).inv.appTop y), ?_⟩
  conv_rhs => rw [← hy]
  rw [AffineSpace.isoOfIsAffine_hom_appTop]
  rfl

/-- The global function on `𝔸(n; S)` given by the monomial with exponent `m`. -/
def monomialFun (S : Scheme.{u}) (n : Type u) (m : n →₀ ℕ) : Γ(𝔸(n; S), ⊤) :=
  polyFun S n (MvPolynomial.monomial m 1)

/-- A coefficient pulled back to a family through the ambient space is pulled back through
the base. -/
theorem toAmbient_appTop_over {T : Over S} (Z : HilbertFamily (affineSpaceOver S n) T d)
    (r : Γ(S, ⊤)) :
    Z.toAmbient.appTop ((𝔸(n; S) ↘ S).appTop r) = Z.structural.appTop (T.hom.appTop r) := by
  have e : Z.toAmbient ≫ (𝔸(n; S) ↘ S) = Z.structural ≫ T.hom := by
    simp only [HilbertFamily.toAmbient, HilbertFamily.structural, Category.assoc]
    exact congrArg (Z.ideal.subschemeι ≫ ·) (familyProjection_comp _ T)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] using
    congrArg (fun φ ↦ φ.appTop.hom r) e

/-- **Monomials span a family over an affine base.** For `S` and `T` affine, the global functions
on a family `Z ⊂ 𝔸(n; T)` are spanned, over the global functions on `T`, by the restrictions of
the monomials. -/
theorem span_monomialFun_eq_top [IsAffine S] {T : Over S} [IsAffine T.left]
    (Z : HilbertFamily (affineSpaceOver S n) T d) :
    letI := Z.structural.appTop.hom.toAlgebra
    Submodule.span Γ(T.left, ⊤)
      (Set.range fun m ↦ Z.toAmbient.appTop (monomialFun S n m)) = ⊤ := by
  let := Z.structural.appTop.hom.toAlgebra
  set N := Submodule.span Γ(T.left, ⊤)
    (Set.range fun m ↦ Z.toAmbient.appTop (monomialFun S n m))
  have hpoly (c : Γ(T.left, ⊤)) (P : MvPolynomial n Γ(S, ⊤)) :
      Z.structural.appTop c * Z.toAmbient.appTop (polyFun S n P) ∈ N := by
    induction P using MvPolynomial.induction_on' with
    | monomial m r =>
      have : polyFun S n (MvPolynomial.monomial m r) =
          (𝔸(n; S) ↘ S).appTop r * monomialFun S n m := by
        simp only [monomialFun, polyFun, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
          map_one, one_mul]
      rw [this, map_mul, toAmbient_appTop_over, ← mul_assoc, ← map_mul]
      exact N.smul_mem _ (Submodule.subset_span ⟨m, rfl⟩)
    | add P Q hP hQ =>
      rw [map_add, map_add, mul_add]
      exact N.add_mem hP hQ
  rw [eq_top_iff]
  rintro y -
  have : IsAffineHom (affineSpaceOver S n).hom := inferInstanceAs (IsAffineHom (𝔸(n; S) ↘ S))
  have : IsAffine ((Over.pullback T.hom).obj (affineSpaceOver S n)).left :=
    inferInstanceAs (IsAffine (pullback _ _))
  obtain ⟨a, rfl⟩ := Z.ideal.subschemeι_app_surjective
    ⟨⊤, isAffineOpen_top ((Over.pullback T.hom).obj (affineSpaceOver S n)).left⟩ y
  have hpo := isPushout_appTop_of_isPullback
    (IsPullback.of_hasPullback (𝔸(n; S) ↘ S) T.hom)
  induction mem_closure_of_isPushout hpo a using AddSubmonoid.closure_induction with
  | mem x hx =>
    obtain ⟨⟨c, b⟩, rfl⟩ := hx
    obtain ⟨P, rfl⟩ := polyFun_surjective S n b
    have := hpoly c P
    simp only [HilbertFamily.structural, HilbertFamily.toAmbient, Scheme.Hom.comp_appTop,
      CommRingCat.hom_comp, RingHom.comp_apply] at this
    change Z.ideal.subschemeι.appTop (_ * _) ∈ N
    rw [map_mul]
    exact this
  | zero =>
    rw [map_zero]
    exact N.zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact N.add_mem hx hy

/-- In a vector space of dimension `d`, a spanning family has a spanning subfamily indexed by
`Fin d`. -/
theorem exists_fin_span_eq_top {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    {d : ℕ} (hd : Module.finrank K V = d) [Module.Finite K V] (v : ι → V)
    (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ f : Fin d → ι, Submodule.span K (Set.range (v ∘ f)) = ⊤ := by
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K v
  let b := Module.Basis.mk hli (by rw [hsp, hv])
  have : Finite κ := Module.Finite.finite_basis b
  have hcard : Nat.card κ = d := by rw [← hd, Module.finrank_eq_nat_card_basis b]
  let e := Finite.equivFinOfCardEq hcard
  refine ⟨a ∘ e.symm, ?_⟩
  rw [← Function.comp_assoc, Set.range_comp, e.symm.surjective.range_eq, Set.image_univ, hsp,
    hv]

/-- **Every family over a field lies in some `F_W`** (condition (2)(c) of Stacks 01JJ in the proof
of Stacks 0B99): a degree-`d` family over the spectrum of a field is a `d`-dimensional quotient
of the polynomial algebra, so `d` of the monomials restrict to a basis of it. -/
theorem exists_mem_chartSubfunctor_of_specField [IsAffine S] (k : Type u) [Field k]
    (g : Spec (.of k) ⟶ S) (Z : HilbertFamily (affineSpaceOver S n) (Over.mk g) d) :
    ∃ W : Fin d → MvPolynomial n Γ(S, ⊤),
      Z ∈ (chartSubfunctor S n d W).obj (Opposite.op (Over.mk g)) := by
  have : IsAffine (Over.mk g).left := inferInstanceAs (IsAffine (Spec _))
  have hK : IsField Γ((Over.mk g).left, ⊤) := isField_Γ_spec k
  let := hK.toField
  let := Z.structural.appTop.hom.toAlgebra
  have hlf : Module.IsFiniteLocallyFreeOfRank Γ((Over.mk g).left, ⊤) Γ(Z.ideal.subscheme, ⊤) d :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_module_of_isAffine Z.structural d
      rfl).mp inferInstance
  have := hlf.finite
  obtain ⟨f, hf⟩ := exists_fin_span_eq_top hlf.finrank_eq _ (span_monomialFun_eq_top Z)
  refine ⟨fun l ↦ MvPolynomial.monomial (f l) 1, fun T'' h _ _ ↦ IsChart.baseChange h ?_⟩
  rw [← surjective_sum_algebraMap_mul_iff] at hf
  intro y
  obtain ⟨c, hc⟩ := hf y
  exact ⟨c, hc⟩

/-- **Over an affine base, `F_W` is the chart condition.** A family over an affine `T` lying in
`F_W(T)` satisfies the chart condition on `T` itself: the cokernel of the chart map has empty
support, since every prime of `Γ(T, 𝒪_T)` is the kernel at the residue field of a point. -/
theorem isChart_of_mem_chartSubfunctor {W : Fin d → MvPolynomial n Γ(S, ⊤)} {T : Over S}
    [IsAffine T.left] {Z : HilbertFamily (affineSpaceOver S n) T d}
    (hZ : Z ∈ (chartSubfunctor S n d W).obj (Opposite.op T)) : IsChart Z W := by
  have hempty : cokernelSupport Z W = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ ?_
    set t := T.left.isoSpec.inv p
    have hK := isField_residueFieldOver T t
    obtain ⟨x, hx⟩ := exists_residueFieldOver_point T t
    have h := (isChart_baseChange_iff (residueFieldOverHom T t) hK Z W).mp
      (hZ _ (residueFieldOverHom T t) inferInstance hK)
    rw [← toSpecΓ_apply_eq_fieldPointPrime _ hK x] at h
    refine h ?_
    rw [hx, ← Scheme.isoSpec_hom]
    change (T.left.isoSpec.inv ≫ T.left.isoSpec.hom) p ∈ _
    rwa [Iso.inv_hom_id]
  let := Z.structural.appTop.hom.toAlgebra
  rw [cokernelSupport, Module.support_eq_empty_iff,
    Submodule.Quotient.subsingleton_iff] at hempty
  exact (surjective_sum_algebraMap_mul_iff (K := Γ(T.left, ⊤))
    (fun l ↦ Z.toAmbient.appTop (polyFun S n (W l)))).mpr hempty

end Stacks.Hilbert

end
