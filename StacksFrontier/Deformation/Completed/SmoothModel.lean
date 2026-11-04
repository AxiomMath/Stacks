module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.GeometricallyRegular.FormalSmoothness

/-!
# A smooth complete local algebra with prescribed cotangent data

For a Noetherian ring `Λ` and a finite ring map `Λ → k` to a field, there is a Noetherian
complete local `Λ`-algebra `R` with residue field `k` which is formally smooth over `Λ` for
the maximal-ideal-adic topology, and whose cotangent data at the residue field is the
expected one: the canonical maps `H₁(L_{k/Λ}) → H₁(L_{k/R})` and
`k ⊗_R Ω[R⁄Λ] → Ω[k⁄Λ]` are both bijective.

## Main definitions

* `Deformation.smoothModel` is the chosen complete local algebra.
* `Deformation.smoothModelResidue` is its canonical map to `k`.

## Main results

* `Deformation.smoothModel_formallySmooth`: the algebra is formally smooth over `Λ` for the
  maximal-ideal-adic topology.
* `Deformation.smoothModel_h1Cotangent_bijective`: the canonical map on first cotangent
  homology is bijective. Since `R → k` is surjective, the target is canonically the conormal
  module `𝔪_R/𝔪_R²`, so this is the conormal description of `H₁(L_{k/Λ})`.
* `Deformation.smoothModel_mapBaseChange_bijective`: the canonical base-change map on
  differentials is bijective.

## Implementation notes

The construction follows the Stacks proof. Start from a polynomial presentation
`Λ[x₁, …, xₙ] ↠ k` and choose finitely many equations in its kernel whose conormal
differentials form a basis of the kernel of `k ⊗ Ω[Λ[x]⁄Λ] → Ω[k⁄Λ]`
(`exists_conormal_differential_basis`). Quotienting by those equations removes exactly that
kernel (`mapBaseChange_bijective_of_quotient_by_conormal_generators`), and the corresponding
Jacobian minor is invertible in `k` (`exists_polynomial_conormal_jacobian_minor`), so
inverting it gives a standard smooth `Λ`-algebra — this performs all the smooth slices at
once. Completing at the kernel of the residue map produces the required complete local
algebra (`completionObjectOfSurjection`); neither formal smoothness
(`formallySmoothNAdic_adicCompletion`) nor the differential comparison
(`mapBaseChange_bijective_of_completion`) is lost in the completion. The first homology
statement then follows from formal smoothness together with Jacobi–Zariski exactness
(`h1Cotangent_map_bijective_of_formallySmoothNAdic`).

The chosen object and the properties it enjoys are packaged in `smoothModelPackage` so that
`smoothModel` itself does not acquire the Noetherian and finiteness hypotheses in its type;
those hypotheses are needed only for the three properties, not to name an object.

Smoothness is stated as adic formal smoothness, `RingHom.FormallySmoothNAdic`; the first
homology and differential assertions are stated as bijectivity of the canonical comparison
maps rather than as the existence of unspecified isomorphisms.

## References

* [Stacks Project, Tag 06SM](https://stacks.math.columbia.edu/tag/06SM)
-/

@[expose] public section

open Algebra
open IsLocalRing
open scoped TensorProduct

universe u v w

namespace Deformation

/-- Composing the base change of `A → C` with a map sending `b ⊗ y` to `b ⊗ map y` recovers the
base-change map on differentials of `A`. -/
private theorem mapBaseChange_comp_eq
    {R A C B : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing B]
    [Algebra R A] [Algebra A C] [Algebra R C]
    [Algebra A B] [Algebra C B] [Algebra R B]
    [IsScalarTower R A C] [IsScalarTower A C B] [IsScalarTower R A B]
    [IsScalarTower R C B]
    (g : B ⊗[A] KaehlerDifferential R A →ₗ[B] B ⊗[C] KaehlerDifferential R C)
    (hg : ∀ (b : B) y, g (b ⊗ₜ[A] y) = b ⊗ₜ[C] KaehlerDifferential.map R R A C y) :
    (KaehlerDifferential.mapBaseChange R C B).comp g =
      KaehlerDifferential.mapBaseChange R A B := by
  have hmap : ((KaehlerDifferential.map R R C B).restrictScalars A).comp
      (KaehlerDifferential.map R R A C) = KaehlerDifferential.map R R A B := by
    apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation R A)
    intro a
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      KaehlerDifferential.map_D]
    exact congrArg (KaehlerDifferential.D R B)
      (IsScalarTower.algebraMap_apply A C B a).symm
  apply TensorProduct.AlgebraTensorModule.ext
  intro b y
  rw [LinearMap.comp_apply, hg, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.mapBaseChange_tmul]
  exact congrArg (fun z => b • z) (DFunLike.congr_fun hmap y)

/-- A `B`-linear map into `B ⊗[C] Ω[C⁄R]` whose range contains every `1 ⊗ D r` is surjective. -/
private theorem surjective_of_tmul_D_mem_range
    {R C B N : Type*} [CommRing R] [CommRing C] [CommRing B] [Algebra R C] [Algebra C B]
    [AddCommGroup N] [Module B N] (f : N →ₗ[B] B ⊗[C] KaehlerDifferential R C)
    (h : ∀ r : C, (1 : B) ⊗ₜ[C] KaehlerDifferential.D R C r ∈ LinearMap.range f) :
    Function.Surjective f := by
  have hgens (y : KaehlerDifferential R C) : (1 : B) ⊗ₜ[C] y ∈ LinearMap.range f := by
    have hy : y ∈ Submodule.span C (Set.range (KaehlerDifferential.D R C)) := by
      rw [KaehlerDifferential.span_range_derivation]
      exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun y _ => (1 : B) ⊗ₜ[C] y ∈ LinearMap.range f) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨r, rfl⟩
      exact h r
    · simp
    · intro y₁ y₂ _ _ hy₁ hy₂
      rw [TensorProduct.tmul_add]
      exact add_mem hy₁ hy₂
    · intro a y _ hy
      rw [TensorProduct.tmul_smul, ← algebraMap_smul B a]
      exact Submodule.smul_mem _ _ hy
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a y =>
    have heq : a ⊗ₜ[C] y = a • ((1 : B) ⊗ₜ[C] y) := by
      simp [TensorProduct.smul_tmul']
    rw [heq]
    exact Submodule.smul_mem _ a (hgens y)
  | add x₁ x₂ hx₁ hx₂ => exact add_mem hx₁ hx₂

/-- If `g` is a surjection as in `mapBaseChange_comp_eq` and the base-change map of `A` is
bijective, so is that of `C`. -/
private theorem mapBaseChange_bijective_of_surjective_comp
    {R A C B : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing B]
    [Algebra R A] [Algebra A C] [Algebra R C]
    [Algebra A B] [Algebra C B] [Algebra R B]
    [IsScalarTower R A C] [IsScalarTower A C B] [IsScalarTower R A B]
    [IsScalarTower R C B]
    (g : B ⊗[A] KaehlerDifferential R A →ₗ[B] B ⊗[C] KaehlerDifferential R C)
    (hg : ∀ (b : B) y, g (b ⊗ₜ[A] y) = b ⊗ₜ[C] KaehlerDifferential.map R R A C y)
    (hsurj : Function.Surjective g)
    (hbij : Function.Bijective (KaehlerDifferential.mapBaseChange R A B)) :
    Function.Bijective (KaehlerDifferential.mapBaseChange R C B) := by
  have hbij' : Function.Bijective (KaehlerDifferential.mapBaseChange R C B ∘ g) := by
    rwa [← LinearMap.coe_comp, mapBaseChange_comp_eq g hg]
  exact (Function.Bijective.of_comp_iff _ ⟨hbij'.1.of_comp, hsurj⟩).mp hbij'

/-- A formally étale extension of the source does not change the differential base-change map
after passage to an algebra over the residue field. -/
public theorem mapBaseChange_bijective_of_formallyEtale
    {R A C B : Type*} [CommRing R] [CommRing A] [CommRing C] [CommRing B]
    [Algebra R A] [Algebra A C] [Algebra R C]
    [Algebra A B] [Algebra C B] [Algebra R B]
    [IsScalarTower R A C] [IsScalarTower A C B] [IsScalarTower R A B]
    [IsScalarTower R C B] [Algebra.FormallyEtale A C]
    (hbij : Function.Bijective (KaehlerDifferential.mapBaseChange R A B)) :
    Function.Bijective (KaehlerDifferential.mapBaseChange R C B) := by
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A C
  let fEquiv : B ⊗[A] KaehlerDifferential R A ≃ₗ[B]
      B ⊗[C] KaehlerDifferential R C :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A C B B
      (KaehlerDifferential R A)).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (.refl _ _) e
  let f : B ⊗[A] KaehlerDifferential R A →ₗ[B]
      B ⊗[C] KaehlerDifferential R C := fEquiv.toLinearMap
  have hf (b : B) (y : KaehlerDifferential R A) :
      f (b ⊗ₜ[A] y) = b ⊗ₜ[C] KaehlerDifferential.map R R A C y := by
    simp only [f, fEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_toLinearMap,
      TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      TensorProduct.AlgebraTensorModule.congr_tmul]
    congr 1
    show KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A C
      (1 ⊗ₜ[A] y) = KaehlerDifferential.map R R A C y
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, one_smul]
  exact mapBaseChange_bijective_of_surjective_comp f hf fEquiv.surjective hbij

/-- If the base-change map on differentials is bijective, the induced map on first cotangent
homology is surjective. -/
public theorem h1Cotangent_map_surjective_of_mapBaseChange_bijective
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hbij : Function.Bijective (KaehlerDifferential.mapBaseChange R A B)) :
    Function.Surjective (Algebra.H1Cotangent.map R A B B) := by
  intro x
  have hδ : Algebra.H1Cotangent.δ R A B x = 0 := by
    apply hbij.1
    simpa using (Algebra.H1Cotangent.exact_δ_mapBaseChange R A B _).2 ⟨x, rfl⟩
  exact (Algebra.H1Cotangent.exact_map_δ R A B x).mp hδ

/-- Once the differential map is bijective, the preceding formal-smoothness injection and the
Jacobi--Zariski exactness give bijectivity on first cotangent homology. -/
public theorem h1Cotangent_map_bijective_of_formallySmoothNAdic
    {A : Type u} {B : Type v} {S : Type w}
    [CommRing A] [CommRing B] [CommRing S]
    [Algebra A B] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    (n : Ideal B)
    (hf : RingHom.FormallySmoothNAdic.{max u w} (algebraMap A B) n)
    (hn : ∃ k : ℕ, 1 ≤ k ∧ n ^ k ≤ RingHom.ker (algebraMap B S))
    (hbij : Function.Bijective (KaehlerDifferential.mapBaseChange A B S)) :
    Function.Bijective (Algebra.H1Cotangent.map A B S S) :=
  ⟨h1Cotangent_map_injective_of_formallySmoothNAdic (n := n) hf hn,
    h1Cotangent_map_surjective_of_mapBaseChange_bijective hbij⟩

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
  [Algebra Λ k] [IsNoetherianRing Λ] [Module.Finite Λ k]

/-- The completion of a `Λ`-algebra `T` at the kernel of a surjection `T → k`, viewed as a
Noetherian complete local `Λ`-algebra with residue field `k`. The kernel is maximal, so the
extended ideal is the maximal ideal of the completion, and finite generation of the kernel
makes the completion complete for that ideal and Noetherian. -/
public noncomputable def completionObjectOfSurjection
    {Λ k T : Type*} [CommRing Λ] [Field k] [CommRing T]
    [Algebra Λ k] [Algebra Λ T]
    (q : T →ₐ[Λ] k) (hq : Function.Surjective q)
    (hfg : (RingHom.ker q.toRingHom).FG) : CompleteLocalAlgCat Λ k := by
  let I : Ideal T := RingHom.ker q.toRingHom
  have hmax : I.IsMaximal := RingHom.ker_isMaximal_of_surjective q.toRingHom hq
  have hmapmax : (I.map (algebraMap T (AdicCompletion I T))).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le I I le_rfl hfg
  let Ic : Ideal (AdicCompletion I T) := I.map (algebraMap T (AdicCompletion I T))
  let : Ic.IsMaximal := hmapmax
  let : IsAdicComplete Ic (AdicCompletion I T) := by
    change IsAdicComplete (I.map (algebraMap T (AdicCompletion I T))) _
    exact AdicCompletion.isAdicComplete_self I hfg
  let : IsLocalRing (AdicCompletion I T) := isLocalRing_of_isAdicComplete_maximal Ic
  let : Algebra Λ (AdicCompletion I T) := inferInstance
  let : IsScalarTower Λ T (AdicCompletion I T) := IsScalarTower.of_algebraMap_eq' rfl
  have hmaxeq : maximalIdeal (AdicCompletion I T) =
      I.map (algebraMap T (AdicCompletion I T)) :=
    (IsLocalRing.eq_maximalIdeal hmapmax).symm
  have hcomplete : IsAdicComplete (maximalIdeal (AdicCompletion I T))
      (AdicCompletion I T) := by
    rw [hmaxeq]
    exact AdicCompletion.isAdicComplete_self I hfg
  have hmaxfg : (maximalIdeal (AdicCompletion I T)).FG := by
    rw [hmaxeq]
    exact hfg.map (algebraMap T (AdicCompletion I T))
  have hnoeth : IsNoetherianRing (AdicCompletion I T) :=
    complete_local_ring_noetherian _ hcomplete hmaxfg
  let : IsLocalRing (AdicCompletion (RingHom.ker q.toRingHom) T) := by
    change IsLocalRing (AdicCompletion I T)
    infer_instance
  let qhat : AdicCompletion I T →ₐ[Λ] k := AdicCompletion.kerProj hq
  have hqhat : Function.Surjective qhat := AdicCompletion.kerProj_surjective hq
  have hker : RingHom.ker qhat.toRingHom = maximalIdeal (AdicCompletion I T) := by
    change RingHom.ker qhat.toRingHom =
      maximalIdeal (AdicCompletion (RingHom.ker q.toRingHom) T)
    exact IsLocalRing.ker_eq_maximalIdeal qhat.toRingHom hqhat
  let : (RingHom.ker qhat.toRingHom).IsTwoSided := inferInstance
  have hres : (AdicCompletion I T ⧸ maximalIdeal (AdicCompletion I T)) ≃ₐ[Λ] k :=
    (Ideal.quotientEquivAlgOfEq Λ hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hqhat)
  exact
    { carrier := AdicCompletion I T
      commRing := inferInstance
      algebra := inferInstance
      completeLocal := ⟨hnoeth, inferInstance, hcomplete⟩
      residueEquiv := hres }

/-- The maximal ideal of `completionObjectOfSurjection q hq hfg` is the ideal generated by the
image of the kernel of `q`. -/
public theorem completionObjectOfSurjection_maximalIdeal
    {Λ k T : Type*} [CommRing Λ] [Field k] [CommRing T]
    [Algebra Λ k] [Algebra Λ T]
    (q : T →ₐ[Λ] k) (hq : Function.Surjective q)
    (hfg : (RingHom.ker q.toRingHom).FG) :
    maximalIdeal (completionObjectOfSurjection q hq hfg) =
      (RingHom.ker q.toRingHom).map
        (algebraMap T (AdicCompletion (RingHom.ker q.toRingHom) T)) := by
  let I : Ideal T := RingHom.ker q.toRingHom
  let : I.IsMaximal := RingHom.ker_isMaximal_of_surjective q.toRingHom hq
  let : (I.map (algebraMap T (AdicCompletion I T))).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le I I le_rfl hfg
  let : IsAdicComplete (I.map (algebraMap T (AdicCompletion I T)))
      (AdicCompletion I T) := AdicCompletion.isAdicComplete_self I hfg
  let : IsLocalRing (AdicCompletion I T) :=
    isLocalRing_of_isAdicComplete_maximal (I.map (algebraMap T (AdicCompletion I T)))
  show maximalIdeal (AdicCompletion I T) = I.map (algebraMap T (AdicCompletion I T))
  exact (IsLocalRing.eq_maximalIdeal
    (AdicCompletion.isMaximal_map_of_le I I le_rfl hfg)).symm

/-- Passing from a finitely generated presentation to its adic completion does not change
the differential module after tensoring with the residue field.  The map need only be
surjective here: density modulo the square of the ideal shows that every residue differential
comes from the presentation. -/
public theorem mapBaseChange_bijective_of_completion
    {Λ T k : Type*} [CommRing Λ] [CommRing T] [Field k]
    [Algebra Λ T] [Algebra Λ k]
    [Algebra T k] [IsScalarTower Λ T k]
    (q : T →ₐ[Λ] k) (hq : Function.Surjective q)
    (hqmap : q.toRingHom = algebraMap T k)
    (hfg : (RingHom.ker q.toRingHom).FG)
    (hbij : Function.Bijective (KaehlerDifferential.mapBaseChange Λ T k)) :
    let C := AdicCompletion (RingHom.ker q.toRingHom) T
    let qhat : C →ₐ[Λ] k := AdicCompletion.kerProj hq
    letI : Algebra C k := qhat.toRingHom.toAlgebra
    let : IsScalarTower Λ C k :=
      IsScalarTower.of_algebraMap_eq' qhat.comp_algebraMap.symm
    Function.Bijective (KaehlerDifferential.mapBaseChange Λ C k) := by
  let I : Ideal T := RingHom.ker q.toRingHom
  let C := AdicCompletion (RingHom.ker q.toRingHom) T
  let : I.IsMaximal := RingHom.ker_isMaximal_of_surjective q.toRingHom hq
  let : (I.map (algebraMap T C)).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le I I le_rfl hfg
  let : IsAdicComplete (I.map (algebraMap T C)) C :=
    AdicCompletion.isAdicComplete_self I hfg
  let : IsLocalRing C := isLocalRing_of_isAdicComplete_maximal
    (I.map (algebraMap T C))
  let : Algebra Λ C := inferInstance
  let : IsScalarTower Λ T C := IsScalarTower.of_algebraMap_eq' rfl
  let qhat : C →ₐ[Λ] k := AdicCompletion.kerProj hq
  let : Algebra C k := qhat.toRingHom.toAlgebra
  let : IsScalarTower Λ C k :=
    IsScalarTower.of_algebraMap_eq' qhat.comp_algebraMap.symm
  have hqhat : qhat.comp (IsScalarTower.toAlgHom Λ T C) = q := by
    ext t
    show AdicCompletion.kerProj hq (AdicCompletion.of I T t) = q t
    exact AdicCompletion.kerProj_of hq t
  let : IsScalarTower T C k :=
    IsScalarTower.of_algebraMap_eq'
      ((congrArg AlgHom.toRingHom hqhat).trans hqmap).symm
  have hmax : maximalIdeal C = I.map (algebraMap T C) :=
    (IsLocalRing.eq_maximalIdeal (AdicCompletion.isMaximal_map_of_le I I le_rfl hfg)).symm
  have hker : RingHom.ker (algebraMap C k) = maximalIdeal C :=
    IsLocalRing.ker_eq_maximalIdeal _ (AdicCompletion.kerProj_surjective hq)
  let v : KaehlerDifferential Λ T →ₗ[T] k ⊗[C] KaehlerDifferential Λ C :=
    ((TensorProduct.mk C k (KaehlerDifferential Λ C) (1 : k)).restrictScalars T).comp
      (KaehlerDifferential.map Λ Λ T C)
  let f : k ⊗[T] KaehlerDifferential Λ T →ₗ[k] k ⊗[C] KaehlerDifferential Λ C :=
    TensorProduct.AlgebraTensorModule.lift
      (LinearMap.toSpanSingleton k _ v)
  have hf_range (r : C) :
      (1 : k) ⊗ₜ[C] KaehlerDifferential.D Λ C r ∈ LinearMap.range f := by
    obtain ⟨t, ht⟩ := exists_sub_algebraMap_mem_pow_map I hfg 2 r
    let z : C := r - algebraMap T C t
    have hzpow : z ∈ (maximalIdeal C) ^ 2 := by
      rw [hmax]
      simpa [z, C, I] using ht
    have hzker : z ∈ RingHom.ker (algebraMap C k) := by
      rw [hker]
      exact (Ideal.pow_le_self (I := maximalIdeal C) (by decide)) hzpow
    have hzd : (1 : k) ⊗ₜ[C] KaehlerDifferential.D Λ C z = 0 := by
      have hzsquare : z ∈ (RingHom.ker (algebraMap C k)) ^ 2 := by
        simpa [hker] using hzpow
      have hz' : (RingHom.ker (algebraMap C k)).toCotangent ⟨z, hzker⟩ = 0 :=
        (Ideal.toCotangent_eq_zero (RingHom.ker (algebraMap C k)) ⟨z, hzker⟩).2 hzsquare
      have hz'' := congrArg (KaehlerDifferential.kerCotangentToTensor Λ C k) hz'
      simpa only [KaehlerDifferential.kerCotangentToTensor_toCotangent, map_zero] using hz''
    have heq : r = algebraMap T C t + z := by
      dsimp [z]
      ring
    rw [heq, map_add, TensorProduct.tmul_add, hzd, add_zero]
    refine ⟨1 ⊗ₜ[T] KaehlerDifferential.D Λ T t, ?_⟩
    rw [← KaehlerDifferential.map_D Λ Λ T C t]
    dsimp [f]
    simp only [LinearMap.toSpanSingleton_apply, one_smul, v,
      LinearMap.comp_apply, LinearMap.restrictScalars_apply]
    rfl
  have hf_tmul (a : k) (y : KaehlerDifferential Λ T) :
      f (a ⊗ₜ[T] y) = a ⊗ₜ[C] KaehlerDifferential.map Λ Λ T C y := by
    change a • ((1 : k) ⊗ₜ[C] KaehlerDifferential.map Λ Λ T C y) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact mapBaseChange_bijective_of_surjective_comp f hf_tmul
    (surjective_of_tmul_D_mem_range f hf_range) hbij

/-- A finite set of equations can be chosen whose conormal differentials form a basis for the
kernel of the differential map to the residue field.  This is the linear algebra step in the
finite slicing construction: the chosen equations are precisely the relations that must be
removed before taking the adic completion. -/
public theorem exists_conormal_differential_basis
    {R A B : Type*} [CommRing R] [CommRing A] [Field B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hsurj : Function.Surjective (algebraMap A B))
    [Module.Finite A (KaehlerDifferential R A)] :
    ∃ (n : ℕ) (f : Fin n → RingHom.ker (algebraMap A B)),
      LinearIndependent B (fun i =>
        KaehlerDifferential.kerCotangentToTensor R A B
          (Ideal.toCotangent _ (f i))) ∧
      Submodule.span B (Set.range (fun i =>
        KaehlerDifferential.kerCotangentToTensor R A B
          (Ideal.toCotangent _ (f i)))) =
        LinearMap.ker (KaehlerDifferential.mapBaseChange R A B) := by
  let c := KaehlerDifferential.kerCotangentToTensor R A B
  have hspan : Submodule.span B (Set.range c) = LinearMap.ker
      (KaehlerDifferential.mapBaseChange R A B) := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, rfl⟩
      have hx := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
        (R := R) (A := A) (B := B) hsurj (c x)).2 ⟨x, rfl⟩
      exact LinearMap.mem_ker.mpr hx
    · intro x hx
      have hrange : x ∈ LinearMap.range c :=
        (KaehlerDifferential.range_kerCotangentToTensor (R := R) (A := A) (B := B)
          hsurj).symm ▸ (show x ∈
            (LinearMap.ker (KaehlerDifferential.mapBaseChange R A B)).restrictScalars A from hx)
      obtain ⟨y, rfl⟩ := hrange
      exact Submodule.subset_span ⟨y, rfl⟩
  obtain ⟨v, hv, hvspan, hvli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq B (Set.range c)
  choose x hx using hv
  choose f hf using fun i => Ideal.toCotangent_surjective _ (x i)
  have heq : (fun i => c (Ideal.toCotangent (RingHom.ker (algebraMap A B)) (f i))) = v := by
    funext i
    rw [hf i, hx i]
  refine ⟨_, f, ?_, ?_⟩
  · rwa [heq]
  · rw [heq]
    exact hvspan.trans hspan

/-- A linearly independent family of rows over a field contains a square minor with
nonzero determinant. -/
public theorem exists_embedding_isUnit_det_submatrix_of_linearIndependent_rows
    {K : Type*} [Field K] {r n : ℕ} (M : Matrix (Fin r) (Fin n) K)
    (hli : LinearIndependent K M.row) :
    ∃ e : Fin r ↪ Fin n, IsUnit (M.submatrix id e).det := by
  classical
  have hrank : M.rank = r := by simpa using hli.rank_matrix
  have hspan : Submodule.span K (Set.range M.col) = ⊤ := by
    rw [Submodule.eq_top_iff_finrank_eq]
    rw [← M.rank_eq_finrank_span_cols, hrank, Module.finrank_pi]
    simp
  let b : Module.Basis (Fin r) K (Fin r → K) := Pi.basisFun K (Fin r)
  let c := Module.Basis.ofSpan hspan.ge
  let φ := b.indexEquiv c
  choose g hg using fun j : Fin r =>
    Module.Basis.ofSpan_subset hspan.ge (Set.mem_range_self (φ j))
  have hginj : Function.Injective g := by
    intro i j hij
    apply φ.injective
    apply c.injective
    rw [← hg i, ← hg j, hij]
  have hcg : M.col ∘ g = ⇑(c.reindex φ.symm) := by
    funext j
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, Function.comp_apply, hg j]
  have hliCols : LinearIndependent K (M.col ∘ g) := by
    rw [hcg]
    exact (c.reindex φ.symm).linearIndependent
  have hspanCols : Submodule.span K (Set.range (M.col ∘ g)) = ⊤ := by
    rw [hcg]
    exact (c.reindex φ.symm).span_eq
  have hdet : IsUnit (b.det (M.col ∘ g)) :=
    b.is_basis_iff_det.mp ⟨hliCols, hspanCols⟩
  refine ⟨⟨g, hginj⟩, ?_⟩
  show IsUnit ((M.submatrix id g).det)
  have hdet' : b.det (M.col ∘ g) = (M.submatrix id g).det := by
    rw [Module.Basis.det_apply]
    rfl
  exact hdet' ▸ hdet

/-- For a polynomial presentation of a field, independent conormal differentials have a
Jacobian minor which is nonzero in the field. -/
public theorem exists_polynomial_conormal_jacobian_minor
    {R B : Type*} [CommRing R] [Field B] [Algebra R B]
    (n m : ℕ) [Algebra (MvPolynomial (Fin n) R) B]
    [IsScalarTower R (MvPolynomial (Fin n) R) B]
    (f : Fin m → RingHom.ker (algebraMap (MvPolynomial (Fin n) R) B))
    (hli : LinearIndependent B (fun i =>
      (1 : B) ⊗ₜ[MvPolynomial (Fin n) R]
        KaehlerDifferential.D R (MvPolynomial (Fin n) R) (f i).1)) :
    ∃ e : Fin m ↪ Fin n,
      IsUnit (((Matrix.of fun i j =>
          algebraMap (MvPolynomial (Fin n) R) B
            (MvPolynomial.pderiv j (f i).1)).submatrix id e).det) := by
  let A := MvPolynomial (Fin n) R
  let b : Module.Basis (Fin n) A (KaehlerDifferential R A) :=
    KaehlerDifferential.mvPolynomialBasis R (Fin n)
  let bB := b.baseChange B
  let w (i : Fin m) := (1 : B) ⊗ₜ[A] KaehlerDifferential.D R A (f i).1
  let M : Matrix (Fin m) (Fin n) B := fun i j =>
    algebraMap A B (MvPolynomial.pderiv j (f i).1)
  let coord : B ⊗[A] KaehlerDifferential R A →ₗ[B] (Fin n → B) :=
    (Finsupp.linearEquivFunOnFinite B B (Fin n)).toLinearMap.comp bB.repr.toLinearMap
  have hcoord : ∀ i j, bB.repr (w i) j = M i j := by
    intro i j
    rw [Module.Basis.baseChange_repr_tmul,
      KaehlerDifferential.mvPolynomialBasis_repr_apply,
      Algebra.smul_def, mul_one]
  have hcoord_inj : Function.Injective coord :=
    (Finsupp.linearEquivFunOnFinite B B (Fin n)).injective.comp bB.repr.injective
  have hliCoord : LinearIndependent B (fun i => coord (w i)) :=
    hli.map' coord (LinearMap.ker_eq_bot.mpr hcoord_inj)
  have hrow : (fun i => coord (w i)) = M.row := by
    funext i
    ext j
    exact hcoord i j
  have hliM : LinearIndependent B M.row := by
    rwa [← hrow]
  obtain ⟨e, he⟩ := exists_embedding_isUnit_det_submatrix_of_linearIndependent_rows M hliM
  show ∃ e : Fin m ↪ Fin n, IsUnit (M.submatrix id e).det
  exact ⟨e, he⟩

/-- Quotienting a surjective presentation by equations whose conormal differentials span the
kernel removes exactly that kernel.  The result is the cotangent base-change isomorphism for
the quotient presentation. -/
public theorem mapBaseChange_bijective_of_quotient_by_conormal_generators
    {R A B : Type*} [CommRing R] [CommRing A] [Field B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (hsurj : Function.Surjective (algebraMap A B))
    (n : ℕ) (f : Fin n → RingHom.ker (algebraMap A B))
    (hspan : Submodule.span B (Set.range (fun i =>
      KaehlerDifferential.kerCotangentToTensor R A B (Ideal.toCotangent _ (f i)))) =
      LinearMap.ker (KaehlerDifferential.mapBaseChange R A B)) :
    let J : Ideal A := Ideal.span (Set.range fun i => (f i).1)
    let A' := A ⧸ J
    let qA : A →ₐ[R] A' := Ideal.Quotient.mkₐ R J
    let q' : A' →+* B :=
      Ideal.Quotient.lift J (algebraMap A B) (by
          change Ideal.span (Set.range fun i => (f i).1) ≤ RingHom.ker (algebraMap A B)
          apply Ideal.span_le.mpr
          rintro x ⟨i, rfl⟩
          exact (f i).2)
    letI : Algebra A' B := q'.toAlgebra
    let : IsScalarTower R A' B :=
      IsScalarTower.of_algebraMap_eq' (by
        ext r
        calc
          algebraMap R B r = q' (algebraMap R A' r) := by
            symm
            calc
              q' (algebraMap R A' r) = q' (algebraMap A A' (algebraMap R A r)) := by
                rw [← qA.commutes r]
                rfl
              _ = algebraMap A B (algebraMap R A r) := by rfl
              _ = algebraMap R B r := (IsScalarTower.algebraMap_apply R A B r).symm)
    Function.Bijective (KaehlerDifferential.mapBaseChange R A' B) := by
  classical
  let J : Ideal A := Ideal.span (Set.range fun i => (f i).1)
  let A' := A ⧸ J
  let qA : A →ₐ[R] A' := Ideal.Quotient.mkₐ R J
  let q' : A' →+* B :=
    Ideal.Quotient.lift J (algebraMap A B) (by
        show Ideal.span (Set.range fun i => (f i).1) ≤ RingHom.ker (algebraMap A B)
        apply Ideal.span_le.mpr
        rintro x ⟨i, rfl⟩
        exact (f i).2)
  let : Algebra A' B := q'.toAlgebra
  have hcomp : q'.comp (algebraMap A A') = algebraMap A B := by
    ext a
    rfl
  have hcompR : (algebraMap A' B).comp (algebraMap R A') = algebraMap R B := by
    ext r
    calc
      q' (algebraMap R A' r) = q' (algebraMap A A' (algebraMap R A r)) := by
        rw [← qA.commutes r]
        rfl
      _ = algebraMap A B (algebraMap R A r) := by rfl
      _ = algebraMap R B r := (IsScalarTower.algebraMap_apply R A B r).symm
  let : IsScalarTower R A' B := IsScalarTower.of_algebraMap_eq' hcompR.symm
  let : IsScalarTower A A' B :=
    IsScalarTower.of_algebraMap_eq' hcomp.symm
  let v : KaehlerDifferential R A →ₗ[A]
      B ⊗[A'] KaehlerDifferential R A' :=
    ((TensorProduct.mk A' B (KaehlerDifferential R A') (1 : B)).restrictScalars A).comp
      (KaehlerDifferential.map R R A A')
  let g : B ⊗[A] KaehlerDifferential R A →ₗ[B]
      B ⊗[A'] KaehlerDifferential R A' :=
    TensorProduct.AlgebraTensorModule.lift (LinearMap.toSpanSingleton B _ v)
  have hkill (i : Fin n) :
      g (KaehlerDifferential.kerCotangentToTensor R A B
        (Ideal.toCotangent _ (f i))) = 0 := by
    rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
    show g (1 ⊗ₜ[A] KaehlerDifferential.D R A (f i).1) = 0
    have hfi : (f i).1 ∈ J := Ideal.subset_span ⟨i, rfl⟩
    have hqfi : algebraMap A A' (f i).1 = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hfi
    simp [g, v, KaehlerDifferential.map_D, hqfi]
  have hspanKill :
      Submodule.span B (Set.range (fun i =>
        KaehlerDifferential.kerCotangentToTensor R A B (Ideal.toCotangent _ (f i)))) ≤
      LinearMap.ker g := by
    rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (hkill i)
  have hg (b : B) (y : KaehlerDifferential R A) :
      g (b ⊗ₜ[A] y) = b ⊗ₜ[A'] KaehlerDifferential.map R R A A' y := by
    change b • ((1 : B) ⊗ₜ[A'] KaehlerDifferential.map R R A A' y) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hcompMap := mapBaseChange_comp_eq g hg
  have hgsurj : Function.Surjective g := by
    refine surjective_of_tmul_D_mem_range g fun a' => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (R := A) (I := J) a'
    refine ⟨1 ⊗ₜ[A] KaehlerDifferential.D R A a, ?_⟩
    simp [hg, KaehlerDifferential.map_D]
    rfl
  constructor
  · intro x y hxy
    obtain ⟨x', hx'⟩ := hgsurj x
    obtain ⟨y', hy'⟩ := hgsurj y
    have hxy' :
        KaehlerDifferential.mapBaseChange R A B x' =
          KaehlerDifferential.mapBaseChange R A B y' := by
      calc
        _ = KaehlerDifferential.mapBaseChange R A' B (g x') :=
          (DFunLike.congr_fun hcompMap x').symm
        _ = KaehlerDifferential.mapBaseChange R A' B (g y') :=
          (congrArg (KaehlerDifferential.mapBaseChange R A' B) hx').trans
            (hxy.trans (congrArg (KaehlerDifferential.mapBaseChange R A' B) hy'.symm))
        _ = _ := DFunLike.congr_fun hcompMap y'
    have hdiff : x' - y' ∈ LinearMap.ker (KaehlerDifferential.mapBaseChange R A B) := by
      rwa [LinearMap.mem_ker, map_sub, sub_eq_zero]
    have hdiffg : x' - y' ∈ LinearMap.ker g := by
      rw [← hspan] at hdiff
      exact hspanKill hdiff
    have hxy'' : g x' = g y' := by
      apply sub_eq_zero.mp
      simpa only [map_sub] using LinearMap.mem_ker.mp hdiffg
    exact hx'.symm.trans (hxy''.trans hy')
  · apply KaehlerDifferential.mapBaseChange_surjective
    intro b
    obtain ⟨a, ha⟩ := hsurj b
    refine ⟨algebraMap A A' a, ?_⟩
    show q' (algebraMap A A' a) = b
    exact (DFunLike.congr_fun hcomp a).trans ha

/-- A formally smooth `Λ`-algebra, with carrier in the universe `max u w`, together with a
surjection onto `k` with finitely generated kernel, such that the base-change map on
differentials at `k` is bijective. -/
public structure SmoothModelPrecompletion (Λ : Type u) (k : Type w)
    [CommRing Λ] [Field k] [Algebra Λ k] where
  /-- The underlying type of the algebra. -/
  carrier : Type (max u w)
  /-- Its ring structure. -/
  commRing : CommRing carrier
  /-- Its `Λ`-algebra structure. -/
  algebra : Algebra Λ carrier
  /-- The residue map onto `k`. -/
  residue : (letI : CommRing carrier := commRing
    letI : Algebra Λ carrier := algebra
    carrier →ₐ[Λ] k)
  /-- The residue map is surjective. -/
  surjective : (letI : CommRing carrier := commRing
    letI : Algebra Λ carrier := algebra
    Function.Surjective residue)
  /-- Its kernel is finitely generated. -/
  kernelFG : (letI : CommRing carrier := commRing
    letI : Algebra Λ carrier := algebra
    (RingHom.ker residue.toRingHom).FG)
  /-- The algebra is formally smooth over `Λ`. -/
  formallySmooth : (letI : CommRing carrier := commRing
    letI : Algebra Λ carrier := algebra
    Algebra.FormallySmooth Λ carrier)
  /-- The canonical base-change map on differentials at `k` is bijective. -/
  mapBaseChangeBijective :
    letI : CommRing carrier := commRing
    letI : Algebra Λ carrier := algebra
    letI : Algebra carrier k := residue.toRingHom.toAlgebra
    let : IsScalarTower Λ carrier k :=
      IsScalarTower.of_algebraMap_eq' residue.comp_algebraMap.symm
    Function.Bijective (KaehlerDifferential.mapBaseChange Λ carrier k)

/-- Lift a finite smooth presentation to the carrier universe of the complete local model. -/
public noncomputable def smoothModelPrecompletionOfSmoothAlgebra
    {Λ : Type u} {k : Type w} {S : Type u}
    [CommRing Λ] [Field k] [Algebra Λ k] [CommRing S] [Algebra Λ S]
    [IsNoetherianRing S]
    (qS : S →ₐ[Λ] k) (hqS : Function.Surjective qS)
    (hformal : Algebra.FormallySmooth Λ S)
    (hbijS :
      letI : Algebra S k := qS.toRingHom.toAlgebra
      let : IsScalarTower Λ S k := IsScalarTower.of_algebraMap_eq' qS.comp_algebraMap.symm
      Function.Bijective (KaehlerDifferential.mapBaseChange Λ S k)) :
    SmoothModelPrecompletion Λ k := by
  let : Algebra S k := qS.toRingHom.toAlgebra
  let : IsScalarTower Λ S k := IsScalarTower.of_algebraMap_eq' qS.comp_algebraMap.symm
  let T := ULift.{max u w} S
  let eST : S ≃ₐ[Λ] T :=
    AlgEquiv.ofRingEquiv (f := ULift.ringEquiv.symm) (by intro a; rfl)
  let qT : T →ₐ[Λ] k := qS.comp eST.symm.toAlgHom
  let : Algebra S T := eST.toAlgHom.toAlgebra
  let : Algebra T k := qT.toRingHom.toAlgebra
  let : IsScalarTower Λ S T := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    exact congrArg ULift.down (eST.commutes a).symm
  have hST : (algebraMap T k).comp (algebraMap S T) = algebraMap S k := by
    ext s
    change qS (eST.symm (eST s)) = qS s
    simp
  have hSTinstance : IsScalarTower S T k := IsScalarTower.of_algebraMap_eq' hST.symm
  let : IsScalarTower S T k := hSTinstance
  let : IsScalarTower Λ T k := IsScalarTower.of_algebraMap_eq' qT.comp_algebraMap.symm
  have hsurjT : Function.Surjective qT := by
    intro b
    obtain ⟨s, hs⟩ := hqS b
    refine ⟨eST s, ?_⟩
    simpa [qT] using hs
  let eSelf : S ≃ₐ[S] T :=
    AlgEquiv.ofRingEquiv (f := eST.toRingEquiv) (by intro s; rfl)
  let : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_equiv eSelf
  let : Algebra.FormallySmooth Λ S := hformal
  have hformalT : Algebra.FormallySmooth Λ T := Algebra.FormallySmooth.of_equiv eST
  have hbijT : Function.Bijective (KaehlerDifferential.mapBaseChange Λ T k) :=
    @mapBaseChange_bijective_of_formallyEtale Λ S T k
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      inferInstance hSTinstance inferInstance inferInstance
      inferInstance hbijS
  let : IsNoetherianRing T := isNoetherianRing_of_ringEquiv S eST.toRingEquiv
  have hfgT : (RingHom.ker qT.toRingHom).FG := IsNoetherian.noetherian _
  exact
    { carrier := T
      commRing := inferInstance
      algebra := inferInstance
      residue := qT
      surjective := hsurjT
      kernelFG := hfgT
      formallySmooth := hformalT
      mapBaseChangeBijective := hbijT }

/-- A smooth finite presentation of `k` whose cotangent map is already an isomorphism. -/
public noncomputable def smoothModelPrecompletion
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    [IsNoetherianRing Λ] [Module.Finite Λ k] : SmoothModelPrecompletion Λ k := by
  classical
  let hgen : ∃ n : ℕ, Nonempty (Algebra.Generators Λ k (Fin n)) :=
    (Algebra.FiniteType.iff_exists_generators (R := Λ) (S := k)).mp inferInstance
  let n := Classical.choose hgen
  let P : Algebra.Generators Λ k (Fin n) := Classical.choice (Classical.choose_spec hgen)
  let A := MvPolynomial (Fin n) Λ
  let q : A →ₐ[Λ] k := MvPolynomial.aeval P.val
  have hq : Function.Surjective q := P.aeval_val_surjective
  let : Algebra A k := q.toRingHom.toAlgebra
  let : IsScalarTower Λ A k := IsScalarTower.of_algebraMap_eq' q.comp_algebraMap.symm
  let : Module.Finite A (KaehlerDifferential Λ A) :=
    Module.Finite.of_basis (KaehlerDifferential.mvPolynomialBasis Λ (Fin n))
  let hcon := exists_conormal_differential_basis (R := Λ) (A := A) (B := k) hq
  let hconSpec := Classical.choose_spec hcon
  let m := Classical.choose hcon
  let f := Classical.choose hconSpec
  let hconProp := Classical.choose_spec hconSpec
  have hli' : LinearIndependent k (fun i =>
      (1 : k) ⊗ₜ[A] KaehlerDifferential.D Λ A (f i).1) := by
    change LinearIndependent k (fun i =>
      (1 : k) ⊗ₜ[A] KaehlerDifferential.D Λ A (Classical.choose hconSpec i).1)
    simpa only [KaehlerDifferential.kerCotangentToTensor_toCotangent] using hconProp.1
  let hminor := exists_polynomial_conormal_jacobian_minor n m f hli'
  let e := Classical.choose hminor
  have he := Classical.choose_spec hminor
  let J : Ideal A := Ideal.span (Set.range fun i => (f i).1)
  let A₀ := A ⧸ J
  let q₀ : A₀ →+* k :=
    Ideal.Quotient.lift J (algebraMap A k) (by
      change J ≤ RingHom.ker (algebraMap A k)
      apply Ideal.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact (f i).2)
  let qA : A →ₐ[Λ] A₀ := Ideal.Quotient.mkₐ Λ J
  let : Algebra A₀ k := q₀.toAlgebra
  let : Algebra A A₀ := qA.toAlgebra
  have hq₀A : (algebraMap A₀ k).comp (algebraMap A A₀) = algebraMap A k := by
    apply RingHom.ext
    intro (a : A)
    change q₀ (Ideal.Quotient.mk J a) = algebraMap A k a
    dsimp [q₀]
    rw [Ideal.Quotient.lift_mk]
  let : IsScalarTower A A₀ k := IsScalarTower.of_algebraMap_eq' hq₀A.symm
  let : Algebra Λ A₀ := inferInstance
  have hq₀R : (algebraMap A₀ k).comp (algebraMap Λ A₀) = algebraMap Λ k := by
    apply RingHom.ext
    intro (a : Λ)
    change q₀ (algebraMap Λ A₀ a) = algebraMap Λ k a
    rw [← qA.commutes a]
    calc
      q₀ (qA (algebraMap Λ A a)) = algebraMap A k (algebraMap Λ A a) :=
        DFunLike.congr_fun hq₀A (algebraMap Λ A a)
      _ = algebraMap Λ k a := (IsScalarTower.algebraMap_apply Λ A k a).symm
  let : IsScalarTower Λ A₀ k := IsScalarTower.of_algebraMap_eq' hq₀R.symm
  have hq₀ : Function.Surjective (algebraMap A₀ k) := by
    intro b
    obtain ⟨a, rfl⟩ := hq b
    refine ⟨algebraMap A A₀ a, ?_⟩
    change algebraMap A₀ k (algebraMap A A₀ a) = algebraMap A k a
    exact DFunLike.congr_fun hq₀A a
  have hbij₀ : Function.Bijective (KaehlerDifferential.mapBaseChange Λ A₀ k) := by
    convert (mapBaseChange_bijective_of_quotient_by_conormal_generators
      (R := Λ) (A := A) (B := k) hq m f hconProp.2) using 1
  let P₀ : Algebra.PreSubmersivePresentation Λ A₀ (Fin n) (Fin m) :=
    Algebra.PreSubmersivePresentation.naive e e.injective
  let M₀ : Matrix (Fin m) (Fin n) A := fun i j => MvPolynomial.pderiv j (f i).1
  let M : Matrix (Fin m) (Fin n) k := M₀.map (algebraMap A k)
  have hmatrix : P₀.jacobiMatrix = (M₀.submatrix id e).transpose := by
    apply Matrix.ext
    intro i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
    change MvPolynomial.pderiv (e i) (f j).1 = M₀ j (e i)
    rfl
  have hjac₀ : P₀.jacobian = algebraMap A A₀ ((M₀.submatrix id e).det) := by
    rw [P₀.jacobian_eq_jacobiMatrix_det, hmatrix, Matrix.det_transpose]
    change algebraMap A A₀ _ = algebraMap A A₀ _
    rfl
  have hdet : q₀ P₀.jacobian = (M.submatrix id e).det := by
    rw [hjac₀]
    calc
      q₀ (algebraMap A A₀ ((M₀.submatrix id e).det)) =
          algebraMap A k ((M₀.submatrix id e).det) := DFunLike.congr_fun hq₀A _
      _ = (M.submatrix id e).det := by
        rw [RingHom.map_det]
        rfl
  have hunit : IsUnit (q₀ P₀.jacobian) := hdet ▸ he
  let S := Localization.Away P₀.jacobian
  let : Algebra A₀ S := inferInstance
  let : IsLocalization.Away P₀.jacobian S := inferInstance
  let : IsScalarTower Λ A₀ S := inferInstance
  have hunit' : IsUnit (algebraMap A₀ k P₀.jacobian) := hunit
  let q₁ : S →ₐ[A₀] k := IsLocalization.Away.liftAlgHom
    (R := A₀) (S := S) (P := k) (f := Algebra.ofId A₀ k) P₀.jacobian hunit'
  let : Algebra S k := q₁.toRingHom.toAlgebra
  let qS : S →ₐ[Λ] k := q₁.restrictScalars Λ
  have hcomp₁ : q₁.comp (IsScalarTower.toAlgHom A₀ A₀ S) = Algebra.ofId A₀ k := by
    ext
  let : IsScalarTower A₀ S k :=
    IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom hcomp₁).symm
  let : IsScalarTower Λ S k := IsScalarTower.of_algebraMap_eq' qS.comp_algebraMap.symm
  have hqS : Function.Surjective qS := by
    intro b
    obtain ⟨a, rfl⟩ := hq₀ b
    exact ⟨algebraMap A₀ S a, by simp [qS, q₁]⟩
  have hfg : (RingHom.ker qS.toRingHom).FG := IsNoetherian.noetherian _
  have hformal : Algebra.FormallySmooth Λ S := by
    let Q : Algebra.PreSubmersivePresentation Λ S (Unit ⊕ Fin n) (Unit ⊕ Fin m) :=
      (Algebra.PreSubmersivePresentation.localizationAway S P₀.jacobian).comp P₀
    have hQ : IsUnit Q.jacobian := by
      rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
        Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
      exact (IsLocalization.Away.algebraMap_isUnit P₀.jacobian).mul
        (IsLocalization.Away.algebraMap_isUnit P₀.jacobian)
    let QS : Algebra.SubmersivePresentation Λ S (Unit ⊕ Fin n) (Unit ⊕ Fin m) :=
      Algebra.SubmersivePresentation.mk Q hQ
    let : Algebra.IsStandardSmooth Λ S := QS.isStandardSmooth
    exact inferInstance
  have hbijS : Function.Bijective (KaehlerDifferential.mapBaseChange Λ S k) :=
    mapBaseChange_bijective_of_formallyEtale
      (R := Λ) (A := A₀) (C := S) (B := k) hbij₀
  exact smoothModelPrecompletionOfSmoothAlgebra qS hqS hformal hbijS

/-- A complete local `Λ`-algebra `R` with residue map `q : R → k` such that, when `Λ` is
Noetherian and `k` is finite over `Λ`, `R` is formally smooth over `Λ` for the
`maximalIdeal R`-adic topology and the maps `Algebra.H1Cotangent.map Λ R k k` and
`KaehlerDifferential.mapBaseChange Λ R k` are bijective. -/
public noncomputable def smoothModelPackage :
    { R : CompleteLocalAlgCat.{u, max u w, w} Λ k //
      let q : R →ₐ[Λ] k := R.residueEquiv.toAlgHom.comp
        (IsScalarTower.toAlgHom Λ R (ResidueField R))
      ∀ (_ : IsNoetherianRing Λ) (_ : Module.Finite Λ k),
        RingHom.FormallySmoothNAdic.{max u w}
          (algebraMap Λ R) (maximalIdeal R) ∧
        (letI : Algebra R k := q.toRingHom.toAlgebra
         letI : IsScalarTower Λ R k :=
           IsScalarTower.of_algebraMap_eq' q.comp_algebraMap.symm
         Function.Bijective (Algebra.H1Cotangent.map Λ R k k) ∧
           Function.Bijective (KaehlerDifferential.mapBaseChange Λ R k)) } := by
  classical
  by_cases h : IsNoetherianRing Λ ∧ Module.Finite Λ k
  · let : IsNoetherianRing Λ := h.1
    let : Module.Finite Λ k := h.2
    let D := smoothModelPrecompletion (Λ := Λ) (k := k)
    let : CommRing D.carrier := D.commRing
    let : Algebra Λ D.carrier := D.algebra
    let R := completionObjectOfSurjection D.residue D.surjective D.kernelFG
    let qhat : R →ₐ[Λ] k := AdicCompletion.kerProj D.surjective
    let qR : R →ₐ[Λ] k := R.residueEquiv.toAlgHom.comp
      (IsScalarTower.toAlgHom Λ R (ResidueField R))
    have hqhat : Function.Surjective qhat :=
      AdicCompletion.kerProj_surjective D.surjective
    have hker : RingHom.ker qhat.toRingHom = maximalIdeal R :=
      IsLocalRing.ker_eq_maximalIdeal qhat.toRingHom hqhat
    have hqR : qR = qhat := by
      ext x
      change ((Ideal.quotientEquivAlgOfEq Λ hker.symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective hqhat))
          (IsLocalRing.residue R x) = qhat x
      change (Ideal.quotientKerAlgEquivOfSurjective hqhat)
        ((Ideal.quotientEquivAlgOfEq Λ hker.symm)
          (Ideal.Quotient.mk (maximalIdeal R) x)) = qhat x
      rw [Ideal.quotientEquivAlgOfEq_mk]
      exact Ideal.quotientKerAlgEquivOfSurjective_mk hqhat x
    have hformal : RingHom.FormallySmoothNAdic.{max u w}
        (algebraMap Λ R) (maximalIdeal R) := by
      let : Algebra.FormallySmooth Λ D.carrier := D.formallySmooth
      let I : Ideal D.carrier := RingHom.ker D.residue.toRingHom
      change RingHom.FormallySmoothNAdic.{max u w}
        (algebraMap Λ (completionObjectOfSurjection D.residue D.surjective D.kernelFG))
        (maximalIdeal (completionObjectOfSurjection D.residue D.surjective D.kernelFG))
      rw [completionObjectOfSurjection_maximalIdeal D.residue D.surjective D.kernelFG]
      change RingHom.FormallySmoothNAdic.{max u w}
        (algebraMap Λ (AdicCompletion I D.carrier))
        (I.map (algebraMap D.carrier (AdicCompletion I D.carrier)))
      exact formallySmoothNAdic_adicCompletion (A := Λ) (B := D.carrier) I D.kernelFG
    have hdiffHat :
        let : Algebra R k := qhat.toRingHom.toAlgebra
        let : IsScalarTower Λ R k :=
          IsScalarTower.of_algebraMap_eq' qhat.comp_algebraMap.symm
        Function.Bijective (KaehlerDifferential.mapBaseChange Λ R k) := by
      let : Algebra D.carrier k := D.residue.toRingHom.toAlgebra
      let : IsScalarTower Λ D.carrier k :=
        IsScalarTower.of_algebraMap_eq' D.residue.comp_algebraMap.symm
      have hbij := mapBaseChange_bijective_of_completion D.residue D.surjective
        rfl D.kernelFG D.mapBaseChangeBijective
      let C := AdicCompletion (RingHom.ker D.residue.toRingHom) D.carrier
      let qhatC : C →ₐ[Λ] k := AdicCompletion.kerProj D.surjective
      let : Algebra C k := qhatC.toRingHom.toAlgebra
      let : IsScalarTower Λ C k :=
        IsScalarTower.of_algebraMap_eq' qhatC.comp_algebraMap.symm
      change Function.Bijective (KaehlerDifferential.mapBaseChange Λ C k)
      exact hbij
    have hdiff :
        let : Algebra R k := qR.toRingHom.toAlgebra
        let : IsScalarTower Λ R k :=
          IsScalarTower.of_algebraMap_eq' qR.comp_algebraMap.symm
        Function.Bijective (KaehlerDifferential.mapBaseChange Λ R k) := by
      rw [hqR]
      exact hdiffHat
    let : Algebra R k := qR.toRingHom.toAlgebra
    let : IsScalarTower Λ R k :=
      IsScalarTower.of_algebraMap_eq' qR.comp_algebraMap.symm
    have hres : Function.Surjective qR := hqR ▸ hqhat
    have hkerR : RingHom.ker (algebraMap R k) = maximalIdeal R :=
      IsLocalRing.ker_eq_maximalIdeal _ hres
    have hkill : ∃ n : ℕ, 1 ≤ n ∧ (maximalIdeal R) ^ n ≤
        RingHom.ker (algebraMap R k) := ⟨1, le_rfl, by simp [hkerR]⟩
    have hh1 : Function.Bijective (Algebra.H1Cotangent.map Λ R k k) :=
      h1Cotangent_map_bijective_of_formallySmoothNAdic
        (A := Λ) (B := R) (S := k) (maximalIdeal R) hformal hkill hdiff
    refine ⟨R, ?_⟩
    intro _ _ _
    exact ⟨hformal, hh1, hdiff⟩
  · let T := ULift.{max u w} k
    let e : k ≃ₐ[Λ] T :=
      AlgEquiv.ofRingEquiv (f := ULift.ringEquiv.symm) (by intro a; rfl)
    let q : T →ₐ[Λ] k := e.symm.toAlgHom
    have hq : Function.Surjective q := e.symm.surjective
    let : IsNoetherianRing T := isNoetherianRing_of_ringEquiv k e.toRingEquiv
    have hfg : (RingHom.ker q.toRingHom).FG := IsNoetherian.noetherian _
    let R := completionObjectOfSurjection q hq hfg
    refine ⟨R, ?_⟩
    intro _ hn hf
    exact (h ⟨hn, hf⟩).elim

/-- A complete local algebra realizing the smooth deformation base. -/
@[stacks 06SM "the object"]
public noncomputable def smoothModel : CompleteLocalAlgCat.{u, max u w, w} Λ k :=
  (smoothModelPackage (Λ := Λ) (k := k)).val

/-- The residue map of the chosen complete local algebra, with its fixed
identification of the residue field with `k`. -/
public noncomputable def smoothModelResidue : smoothModel (Λ := Λ) (k := k) →ₐ[Λ] k :=
  (smoothModel (Λ := Λ) (k := k)).residueEquiv.toAlgHom.comp
    (IsScalarTower.toAlgHom Λ (smoothModel (Λ := Λ) (k := k))
      (ResidueField (smoothModel (Λ := Λ) (k := k))))

/-- The chosen complete local algebra is formally smooth over `Λ` for the maximal-ideal-adic
topology. -/
@[stacks 06SM "smoothness"]
public theorem smoothModel_formallySmooth :
    RingHom.FormallySmoothNAdic.{max u w}
      (algebraMap Λ (smoothModel (Λ := Λ) (k := k)))
      (maximalIdeal (smoothModel (Λ := Λ) (k := k))) :=
  ((smoothModelPackage (Λ := Λ) (k := k)).property inferInstance inferInstance).1

/-- For the chosen complete local algebra `R`, the canonical map
`H₁(L_{k/Λ}) → H₁(L_{k/R})` is bijective. Since `R → k` is surjective the target is
canonically the conormal module `𝔪_R/𝔪_R²`, so this is the conormal description of
`H₁(L_{k/Λ})`. -/
@[stacks 06SM "first cotangent homology"]
public theorem smoothModel_h1Cotangent_bijective :
    let R := smoothModel (Λ := Λ) (k := k)
    letI : Algebra R k := (smoothModelResidue (Λ := Λ) (k := k)).toRingHom.toAlgebra
    letI : IsScalarTower Λ R k :=
      IsScalarTower.of_algebraMap_eq'
        (smoothModelResidue (Λ := Λ) (k := k)).comp_algebraMap.symm
    Function.Bijective (Algebra.H1Cotangent.map Λ R k k) := by
  exact ((smoothModelPackage (Λ := Λ) (k := k)).property
    inferInstance inferInstance).2.1

/-- For the chosen complete local algebra `R`, the canonical base-change map
`k ⊗_R Ω[R⁄Λ] → Ω[k⁄Λ]` is bijective. -/
@[stacks 06SM "differentials"]
public theorem smoothModel_mapBaseChange_bijective :
    let R := smoothModel (Λ := Λ) (k := k)
    letI : Algebra R k := (smoothModelResidue (Λ := Λ) (k := k)).toRingHom.toAlgebra
    letI : IsScalarTower Λ R k :=
      IsScalarTower.of_algebraMap_eq'
        (smoothModelResidue (Λ := Λ) (k := k)).comp_algebraMap.symm
    Function.Bijective (KaehlerDifferential.mapBaseChange Λ R k) := by
  exact ((smoothModelPackage (Λ := Λ) (k := k)).property
    inferInstance inferInstance).2.2

end Deformation
