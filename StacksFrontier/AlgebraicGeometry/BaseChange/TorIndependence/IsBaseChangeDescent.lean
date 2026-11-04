module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Base changes along pushouts and along jointly surjective flat families

Two pieces of linear algebra used to move the base-change property of Stacks 0DJ7 between
commutative squares of rings.

## Main results

* `RingTheory.TorIndependence.isBaseChange_of_isBaseChange_of_span`: a `C`-linear map which is a
  base change along `T → T'` is a base change along `C → C'`, when `C'` is spanned over `T'` by
  the image of `C`.
* `RingTheory.TorIndependence.bijective_of_forall_bijective_lTensor`: a linear map which becomes
  bijective after base change to every member of a jointly surjective family of flat algebras is
  bijective.
* `RingTheory.TorIndependence.isBaseChange_of_forall_isBaseChange_comp`: the base-change property
  descends along such a family.

## References

* [Stacks Project, Tag 00HN](https://stacks.math.columbia.edu/tag/00HN)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public section

open scoped TensorProduct

namespace RingTheory.TorIndependence

/-! ### Base change along a pushout of the scalars -/

section Pushout

/-- Scalars from `C` and `T'` commute on a `C'`-module on which both act through `C'`. -/
private theorem smulCommClass_of_isScalarTower (C C' T' X : Type*) [CommRing C] [CommRing C']
    [CommRing T'] [Algebra C C'] [Algebra T' C'] [AddCommMonoid X] [Module C' X] [Module C X]
    [Module T' X] [IsScalarTower C C' X] [IsScalarTower T' C' X] : SMulCommClass C T' X :=
  ⟨fun c t n => by
    rw [← algebraMap_smul C' c (t • n), ← algebraMap_smul C' t n, ← algebraMap_smul C' t (c • n),
      ← algebraMap_smul C' c n, smul_smul, smul_smul, mul_comm]⟩

/-- **Base change along a pushout of the scalars.** Let `T → T'` and `T → C → C'`, `T' → C'` be
ring maps such that `C'` is spanned over `T'` by the image of `C`. If a `C`-linear map
`j : M → N` into a `C'`-module is a base change along `T → T'`, it is a base change along
`C → C'`. -/
theorem isBaseChange_of_isBaseChange_of_span {T T' C C' : Type*} [CommRing T] [CommRing T']
    [CommRing C] [CommRing C'] [Algebra T T'] [Algebra T C] [Algebra C C'] [Algebra T' C']
    [Algebra T C'] [IsScalarTower T T' C'] [IsScalarTower T C C']
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module C M] [Module T M]
    [IsScalarTower T C M] [Module C' N] [Module C N] [Module T' N] [Module T N]
    [IsScalarTower C C' N] [IsScalarTower T' C' N] [IsScalarTower T T' N] [IsScalarTower T C N]
    (j : M →ₗ[C] N) (hj : IsBaseChange T' (j.restrictScalars T))
    (hspan : ∀ x : C', x ∈ Submodule.span T' (Set.range (algebraMap C C'))) :
    IsBaseChange C' j := by
  refine IsBaseChange.of_lift_unique _ fun Q _ _ _ _ g => ?_
  let : Module T' Q := Module.compHom Q (algebraMap T' C')
  have : IsScalarTower T' C' Q := IsScalarTower.of_compHom _ _ _
  let : Module T Q := Module.compHom Q (algebraMap T C')
  have : IsScalarTower T T' Q := ⟨fun t t' q => by
    change algebraMap T' C' (t • t') • q = algebraMap T C' t • (algebraMap T' C' t' • q)
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_smul]⟩
  have : SMulCommClass C T' N := smulCommClass_of_isScalarTower C C' T' N
  have : SMulCommClass C T' Q := smulCommClass_of_isScalarTower C C' T' Q
  have : IsScalarTower T C Q := ⟨fun t c q => by
    change (t • c) • q = algebraMap T C' t • (c • q)
    rw [Algebra.smul_def, mul_smul, ← algebraMap_smul C' (algebraMap T C t),
      ← IsScalarTower.algebraMap_apply]⟩
  let g' : N →ₗ[T'] Q := hj.lift (g.restrictScalars T)
  have hg' : ∀ m, g' (j m) = g m := fun m => hj.lift_eq _ m
  have hC : ∀ (c : C) (n : N), g' (c • n) = c • g' n := fun c => LinearMap.congr_fun
    (hj.algHom_ext (g' ∘ₗ DistribSMul.toLinearMap T' N c)
      (DistribSMul.toLinearMap T' Q c ∘ₗ g') fun m => by
        change g' (c • j m) = c • g' (j m)
        rw [← j.map_smul, hg', hg', g.map_smul])
  have hC' : ∀ (x : C') (n : N), g' (x • n) = x • g' n := by
    intro x n
    refine Submodule.span_induction (p := fun x _ => g' (x • n) = x • g' n) ?_ ?_ ?_ ?_
      (hspan x)
    · rintro _ ⟨c, rfl⟩
      rw [algebraMap_smul, algebraMap_smul]
      exact hC c n
    · rw [zero_smul, map_zero, zero_smul]
    · intro x y _ _ hx hy
      rw [add_smul, map_add, hx, hy, add_smul]
    · intro t x _ hx
      rw [smul_assoc, map_smul, hx, smul_assoc]
  let G : N →ₗ[C'] Q := { toFun := g', map_add' := g'.map_add, map_smul' := hC' }
  refine ⟨G, LinearMap.ext hg', fun G' hG' => LinearMap.ext fun n => LinearMap.congr_fun
    (hj.algHom_ext (G'.restrictScalars T') g' fun m => by
      change G' (j m) = g' (j m)
      rw [hg']
      exact LinearMap.congr_fun hG' m) n⟩

end Pushout

/-! ### Descent of bijectivity along a jointly surjective family of flat algebras -/

section Family

variable {T : Type*} [CommRing T] {ι : Sort*} (B : ι → Type*) [∀ i, CommRing (B i)]
  [∀ i, Algebra T (B i)] [∀ i, Module.Flat T (B i)]

/-- A module killed by base change to every member of a jointly surjective family of flat
algebras is zero. -/
theorem subsingleton_of_forall_subsingleton_tensor
    (hB : ∀ q : PrimeSpectrum T, ∃ i, q ∈ Set.range (PrimeSpectrum.comap (algebraMap T (B i))))
    {M : Type*} [AddCommGroup M] [Module T M] (hM : ∀ i, Subsingleton (B i ⊗[T] M)) :
    Subsingleton M := by
  refine subsingleton_of_forall_eq 0 fun m => ?_
  by_contra hm
  let I := Ideal.torsionOf T M m
  have hI : I ≠ ⊤ := fun h => hm (by
    have h1 : (1 : T) ∈ I := h ▸ Submodule.mem_top
    simpa [I, Ideal.mem_torsionOf_iff] using h1)
  obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨i, Q, hQ⟩ := hB ⟨P, hP.isPrime⟩
  let e := Ideal.quotTorsionOfEquivSpanSingleton T M m
  let ι' : (T ⧸ I) →ₗ[T] M := (T ∙ m).subtype ∘ₗ e.toLinearMap
  have hinj : Function.Injective (ι'.lTensor (B i)) :=
    Module.Flat.lTensor_preserves_injective_linearMap ι'
      ((Submodule.injective_subtype _).comp e.injective)
  have := hM i
  have : Subsingleton (B i ⊗[T] (T ⧸ I)) := hinj.subsingleton
  have : Subsingleton (B i ⧸ I.map (algebraMap T (B i))) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (B i) I).toEquiv.subsingleton
  have htop : I.map (algebraMap T (B i)) = ⊤ := Ideal.Quotient.subsingleton_iff.mp inferInstance
  have hle : I.map (algebraMap T (B i)) ≤ Q.asIdeal := by
    rw [Ideal.map_le_iff_le_comap,
      show Q.asIdeal.comap (algebraMap T (B i)) = P from congrArg PrimeSpectrum.asIdeal hQ]
    exact hIP
  exact Q.isPrime.ne_top (top_le_iff.mp (htop ▸ hle))

/-- A linear map which becomes bijective after base change to every member of a jointly
surjective family of flat algebras is bijective. -/
theorem bijective_of_forall_bijective_lTensor
    (hB : ∀ q : PrimeSpectrum T, ∃ i, q ∈ Set.range (PrimeSpectrum.comap (algebraMap T (B i))))
    {M N : Type*} [AddCommGroup M] [Module T M] [AddCommGroup N] [Module T N] (L : M →ₗ[T] N)
    (hL : ∀ i, Function.Bijective (L.lTensor (B i))) : Function.Bijective L := by
  constructor
  · have hk : Subsingleton (LinearMap.ker L) := by
      refine subsingleton_of_forall_subsingleton_tensor B hB fun i => ?_
      have hinj : Function.Injective ((LinearMap.ker L).subtype.lTensor (B i)) :=
        Module.Flat.lTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
      refine ⟨fun x y => hinj ((hL i).1 ?_)⟩
      rw [← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      have : L ∘ₗ (LinearMap.ker L).subtype = 0 := LinearMap.ext fun z => z.2
      rw [this, LinearMap.lTensor_zero]
      rfl
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : LinearMap.ker L) 0)
  · have hc : Subsingleton (N ⧸ LinearMap.range L) := by
      refine subsingleton_of_forall_subsingleton_tensor B hB fun i => ?_
      have hsurj : Function.Surjective ((LinearMap.range L).mkQ.lTensor (B i)) :=
        LinearMap.lTensor_surjective _ (Submodule.mkQ_surjective _)
      refine ⟨fun x y => ?_⟩
      obtain ⟨x, rfl⟩ := hsurj x
      obtain ⟨y, rfl⟩ := hsurj y
      obtain ⟨x, rfl⟩ := (hL i).2 x
      obtain ⟨y, rfl⟩ := (hL i).2 y
      have h0 : (LinearMap.range L).mkQ ∘ₗ L = 0 := LinearMap.range_mkQ_comp L
      simp only [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, h0, LinearMap.lTensor_zero,
        LinearMap.zero_apply]
    rw [← LinearMap.range_eq_top]
    exact Submodule.Quotient.subsingleton_iff.mp hc

end Family

/-- If `h` and `h ∘ g` are base changes along `T → T₁`, then `g` becomes bijective after base
change to `T₁`. -/
theorem bijective_lTensor_of_isBaseChange {T T₁ : Type*} [CommRing T] [CommRing T₁] [Algebra T T₁]
    {N P Q : Type*} [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [Module T N] [Module T P]
    [Module T Q] [Module T₁ Q] [IsScalarTower T T₁ Q] (g : N →ₗ[T] P) (h : P →ₗ[T] Q)
    (hh : IsBaseChange T₁ h) (hhg : IsBaseChange T₁ (h ∘ₗ g)) :
    Function.Bijective (g.lTensor T₁) := by
  have key : ∀ x, g.lTensor T₁ x = hh.equiv.symm (hhg.equiv x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
    | tmul t n =>
      rw [LinearMap.lTensor_tmul, IsBaseChange.equiv_tmul, LinearEquiv.map_smul,
        LinearMap.comp_apply, IsBaseChange.equiv_symm_apply, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
  rw [show ⇑(g.lTensor T₁) = hh.equiv.symm ∘ hhg.equiv from funext key]
  exact hh.equiv.symm.bijective.comp hhg.equiv.bijective

/-- **Descent of the base-change property along a jointly surjective flat family.** Let
`q : H → H'` be `C`-linear with `H'` a `T`-module, and for each `i` let `j' i : H' → H₁' i` be a
base change along the flat `T → T₁ i`. If every `j' i ∘ q` is a base change along `C → T₁ i` and
the `T₁ i` jointly cover `Spec T`, then `q` is a base change along `C → T`. -/
theorem isBaseChange_of_forall_isBaseChange_comp {C T : Type*} [CommRing C] [CommRing T]
    [Algebra C T] {ι : Sort*} (T₁ : ι → Type*) [∀ i, CommRing (T₁ i)] [∀ i, Algebra T (T₁ i)]
    [∀ i, Algebra C (T₁ i)] [∀ i, IsScalarTower C T (T₁ i)] [∀ i, Module.Flat T (T₁ i)]
    (hB : ∀ q : PrimeSpectrum T, ∃ i, q ∈ Set.range (PrimeSpectrum.comap (algebraMap T (T₁ i))))
    {H H' : Type*} [AddCommGroup H] [AddCommGroup H'] [Module C H] [Module C H'] [Module T H']
    [IsScalarTower C T H'] (H₁' : ι → Type*) [∀ i, AddCommGroup (H₁' i)]
    [∀ i, Module C (H₁' i)] [∀ i, Module T (H₁' i)] [∀ i, Module (T₁ i) (H₁' i)]
    [∀ i, IsScalarTower C T (H₁' i)] [∀ i, IsScalarTower T (T₁ i) (H₁' i)]
    [∀ i, IsScalarTower C (T₁ i) (H₁' i)]
    (q : H →ₗ[C] H') (j' : ∀ i, H' →ₗ[T] H₁' i) (hj' : ∀ i, IsBaseChange (T₁ i) (j' i))
    (h : ∀ i, IsBaseChange (T₁ i) (((j' i).restrictScalars C) ∘ₗ q)) :
    IsBaseChange T q := by
  have hmk := TensorProduct.isBaseChange C H T
  let L : T ⊗[C] H →ₗ[T] H' := hmk.lift q
  have hL : (L.restrictScalars C) ∘ₗ TensorProduct.mk C T H 1 = q := hmk.lift_comp q
  have hbij : Function.Bijective L := by
    refine bijective_of_forall_bijective_lTensor T₁ hB L fun i => ?_
    refine bijective_lTensor_of_isBaseChange L (j' i) (hj' i) ?_
    refine hmk.of_comp ?_
    rw [← hL] at h
    exact h i
  refine (IsBaseChange.iff_of_equiv_comm (LinearEquiv.refl C H) (LinearEquiv.ofBijective L hbij)
    ?_).mp hmk
  exact LinearMap.ext fun x => (LinearMap.congr_fun hL x).symm

/-- If `h` is a base change along `T → T₁`, then `h ∘ g` is one exactly when `g` becomes bijective
after base change to `T₁`. -/
theorem isBaseChange_comp_iff_bijective_lTensor {T T₁ : Type*} [CommRing T] [CommRing T₁]
    [Algebra T T₁] {N P Q : Type*} [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module T N] [Module T P] [Module T Q] [Module T₁ Q] [IsScalarTower T T₁ Q]
    (g : N →ₗ[T] P) (h : P →ₗ[T] Q) (hh : IsBaseChange T₁ h) :
    IsBaseChange T₁ (h ∘ₗ g) ↔ Function.Bijective (g.lTensor T₁) := by
  refine ⟨bijective_lTensor_of_isBaseChange g h hh, fun hg => ?_⟩
  let e : T₁ ⊗[T] N ≃ₗ[T₁] Q :=
    (LinearEquiv.ofBijective (TensorProduct.AlgebraTensorModule.lTensor T₁ T₁ g) hg).trans hh.equiv
  refine IsBaseChange.of_equiv e fun n => ?_
  change hh.equiv ((1 : T₁) ⊗ₜ[T] g n) = h (g n)
  rw [IsBaseChange.equiv_tmul, one_smul]

/-- A `C`-linear map `q : H → H'` into a `T`-module is a base change along `C → T` exactly when the
induced `T`-linear map `T ⊗_C H → H'` is bijective. -/
theorem isBaseChange_iff_bijective_lift {C T : Type*} [CommRing C] [CommRing T] [Algebra C T]
    {H H' : Type*} [AddCommGroup H] [AddCommGroup H'] [Module C H] [Module C H'] [Module T H']
    [IsScalarTower C T H'] (q : H →ₗ[C] H') :
    IsBaseChange T q ↔ Function.Bijective ((TensorProduct.isBaseChange C H T).lift q) := by
  have hmk := TensorProduct.isBaseChange C H T
  have hL : ((hmk.lift q).restrictScalars C) ∘ₗ TensorProduct.mk C T H 1 = q := hmk.lift_comp q
  refine ⟨fun hq => ?_, fun hbij => ?_⟩
  · have : (hmk.lift q : T ⊗[C] H → H') = hq.equiv := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | add x y hx hy => rw [map_add, map_add, hx, hy]
      | tmul t m =>
        have h1 : (t ⊗ₜ[C] m : T ⊗[C] H) = t • ((1 : T) ⊗ₜ[C] m) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [IsBaseChange.equiv_tmul, h1, LinearMap.map_smul]
        exact congrArg (t • ·) (LinearMap.congr_fun hL m)
    rw [this]
    exact hq.equiv.bijective
  · refine (IsBaseChange.iff_of_equiv_comm (LinearEquiv.refl C H)
      (LinearEquiv.ofBijective (hmk.lift q) hbij) ?_).mp hmk
    exact LinearMap.ext fun x => (LinearMap.congr_fun hL x).symm

end RingTheory.TorIndependence
