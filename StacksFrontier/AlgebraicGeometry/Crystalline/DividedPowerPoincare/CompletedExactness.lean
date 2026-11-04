module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.CompletedForms
import all StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.CompletedRing
import all StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare.CompletedForms

/-!
# The divided power Poincaré lemma: the completed assertion

The last part of `StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerPoincare`: modulo `pᵉ`
the completed de Rham complex is the de Rham complex of `P/pᵉ`, the contracting homotopy of the
uncompleted complex descends, and the completed complex
`0 → M → M ⊗̂_A D → M ⊗̂_A Ω¹_D → ⋯` is exact for every `p`-adically complete `A`-module `M`
(`Crystalline.CompletedPoincare.completedDeRham_tensor_augmentation_injective`,
`Crystalline.CompletedPoincare.completedDeRham_tensor_exact_augmentation`,
`Crystalline.CompletedPoincare.completedDeRham_tensor_exact`).

## References

* [Stacks Project, Tag 07LC](https://stacks.math.columbia.edu/tag/07LC)
-/
@[expose] public section

universe u v w uA uW uM

namespace Crystalline

attribute [local implicit_reducible] RestrictScalars

open DividedPowers
open scoped TensorProduct

namespace CompletedPoincare

noncomputable section

variable (p : ℕ) (A : Type uA) [CommRing A] (W : Type uW)

variable (cdp : ContinuousDividedPowers p A W)

variable (M : Type uM) [AddCommGroup M] [Module A M]

section IsAlt

variable {S N P : Type*} [CommSemiring S] [AddCommMonoid N] [Module S N]
  [AddCommMonoid P] [Module S P]

end IsAlt

private def exteriorPowerMap
    {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Module S Y]
    [IsScalarTower R S Y] (f : X →ₗ[R] Y) (n : ℕ) :
    (⋀[R]^n X) →ₗ[R] (⋀[S]^n Y) :=
  exteriorPower.alternatingMapLinearEquiv
    (({ (exteriorPower.ιMulti S n (M := Y)).toMultilinearMap.restrictScalars R with
      map_eq_zero_of_eq' := fun v _ _ h hij =>
        (exteriorPower.ιMulti S n).map_eq_zero_of_eq v h hij } :
      Y [⋀^Fin n]→ₗ[R] (⋀[S]^n Y)).compLinearMap f)

private theorem exteriorPowerMap_ιMulti
    {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Module S Y]
    [IsScalarTower R S Y] (f : X →ₗ[R] Y) (n : ℕ) (v : Fin n → X) :
    exteriorPowerMap f n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (fun i => f (v i)) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

private theorem isBaseChange_of_quotientEquiv
    {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Module S Y]
    [IsScalarTower R S Y] (f : X →ₗ[R] Y)
    (hs : Function.Surjective (algebraMap R S))
    (K : Ideal R) (hK : K = RingHom.ker (algebraMap R S))
    (E : (X ⧸ K • (⊤ : Submodule R X)) ≃ₗ[R] Y)
    (hE : ∀ x, E (Submodule.Quotient.mk x) = f x) :
    IsBaseChange S f := by
  apply IsBaseChange.of_lift_unique _
  intro Q _ _ _ _ g
  let _ := Module.addCommMonoidToAddCommGroup S (M := Q)
  have hg : K • (⊤ : Submodule R X) ≤ g.ker := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr x hx => ?_) (fun x y hx hy => ?_)
    · change g (r • x) = 0
      rw [map_smul, ← IsScalarTower.algebraMap_smul S]
      have hr' : algebraMap R S r = 0 := by
        have : r ∈ RingHom.ker (algebraMap R S) := hK ▸ hr
        exact this
      rw [hr', zero_smul]
    · exact g.ker.add_mem hx hy
  let L := (K • (⊤ : Submodule R X)).liftQ g hg
  refine ⟨LinearMap.extendScalarsOfSurjective hs (L.comp E.symm.toLinearMap), ?_, ?_⟩
  · ext x
    change L (E.symm (f x)) = g x
    rw [← hE, E.symm_apply_apply]
    rfl
  · intro F hF
    ext y
    obtain ⟨z, rfl⟩ := E.surjective y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
    change F (E (Submodule.Quotient.mk x)) = L (E.symm (E (Submodule.Quotient.mk x)))
    rw [E.symm_apply_apply, hE]
    exact LinearMap.congr_fun hF x

private def quotientEquivOfIsBaseChange
    {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [Module S Y]
    [IsScalarTower R S Y] (f : X →ₗ[R] Y)
    (hs : Function.Surjective (algebraMap R S))
    (K : Ideal R) (hK : K = RingHom.ker (algebraMap R S))
    (hf : IsBaseChange S f) :
    { E : (X ⧸ K • (⊤ : Submodule R X)) ≃ₗ[R] Y //
      ∀ x, E (Submodule.Quotient.mk x) = f x } := by
  let e : (R ⧸ K) ≃ₐ[R] S := (Ideal.quotientEquivAlgOfEq R hK).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R S) hs)
  refine ⟨(TensorProduct.quotTensorEquivQuotSMul X K).symm.trans
    ((TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R X)).trans
      (hf.equiv.restrictScalars R)), ?_⟩
  intro x
  simp [TensorProduct.quotTensorEquivQuotSMul_symm_mk, IsBaseChange.equiv_tmul]




section Maps
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
  {J : Ideal B} {K : Ideal C} (δ : DividedPowers J) (ε : DividedPowers K)
  (h : δ.IsDPMorphism ε (algebraMap B C))

private def dpDifferentialsMap :
    dividedPowerDifferentials (A := A) δ →ₗ[B] dividedPowerDifferentials (A := A) ε where
  __ := mapDifferentialsOfDPMorphism (A := A) (J := J) (delta := δ) ε
    (IsScalarTower.toAlgHom A B C) h
  map_smul' b x :=
    (mapDifferentialsOfDPMorphism_smul (A := A) (J := J) (delta := δ)
      ε (IsScalarTower.toAlgHom A B C) h b x).trans
      (IsScalarTower.algebraMap_smul C b _)

private theorem dpDifferentialsMap_d (b : B) :
    dpDifferentialsMap (A := A) δ ε h (dividedPowerDifferential (A := A) δ b) =
      dividedPowerDifferential (A := A) ε (algebraMap B C b) :=
  mapDifferentialsOfDPMorphism_d (A := A) (J := J) (delta := δ) ε
    (IsScalarTower.toAlgHom A B C) h b

private def dpFormsMap (n : ℕ) :
    dividedPowerDifferentialForms (A := A) δ n →ₗ[B]
      dividedPowerDifferentialForms (A := A) ε n :=
  exteriorPowerMap (S := C) (dpDifferentialsMap (A := A) δ ε h) n

private theorem dpFormsMap_generator (n : ℕ) (b : Fin (n + 1) → B) :
    dpFormsMap (A := A) δ ε h n
      (b 0 • exteriorPower.ιMulti B n (fun j => dividedPowerDifferential (A := A) δ (b j.succ))) =
      algebraMap B C (b 0) • exteriorPower.ιMulti C n
        (fun j => dividedPowerDifferential (A := A) ε (algebraMap B C (b j.succ))) := by
  rw [map_smul, dpFormsMap, exteriorPowerMap_ιMulti]
  simp only [dpDifferentialsMap_d, IsScalarTower.algebraMap_smul]

private lemma exactForms_span {R S X : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup X] [Module S X] [Module R X] [IsScalarTower R S X]
    (D : S → X) (hD : Submodule.span S (Set.range D) = ⊤) (i : ℕ) :
    Submodule.span R (Set.range fun f : Fin (i + 1) → S ↦
      f 0 • exteriorPower.ιMulti S i (fun j ↦ D (f j.succ))) = ⊤ := by
  have hw : Submodule.span S (Set.range fun f : Fin i → S ↦
      exteriorPower.ιMulti S i (fun j ↦ D (f j))) = ⊤ := by
    have himg : exteriorPower.ιMulti S i ''
        {a : Fin i → X | Set.range a ⊆ Set.range D} =
        Set.range (fun f : Fin i → S ↦ exteriorPower.ιMulti S i (fun j ↦ D (f j))) := by
      ext x; constructor
      · rintro ⟨a, ha, rfl⟩; choose f hf using fun j ↦ ha (Set.mem_range_self j)
        exact ⟨f, congrArg _ (funext hf)⟩
      · rintro ⟨f, rfl⟩; exact ⟨_, Set.range_subset_iff.mpr (fun j ↦ ⟨f j, rfl⟩), rfl⟩
    rw [← himg]; exact exteriorPower.ιMulti_span_of_span S i X hD
  open scoped Pointwise in
    have hset : (Set.univ : Set S) • (Set.range fun f : Fin i → S ↦
        exteriorPower.ιMulti S i (fun j ↦ D (f j))) =
        Set.range (fun f : Fin (i + 1) → S ↦
          f 0 • exteriorPower.ιMulti S i (fun j ↦ D (f j.succ))) := by
      ext x; constructor
      · rintro ⟨c, -, _, ⟨f, rfl⟩, rfl⟩; exact ⟨Fin.cons c f, by simp⟩
      · rintro ⟨f, rfl⟩; exact Set.smul_mem_smul (Set.mem_univ _) ⟨fun j ↦ f j.succ, rfl⟩
  rw [← hset, Submodule.span_smul_of_span_eq_top Submodule.span_univ,
    hw, Submodule.restrictScalars_top]

private theorem dpFormsMap_comm (n : ℕ) :
    ((dividedPowerDeRhamComplex (A := A) ε).differential n).comp
        ((dpFormsMap (A := A) δ ε h n).restrictScalars A) =
      ((dpFormsMap (A := A) δ ε h (n + 1)).restrictScalars A).comp
        ((dividedPowerDeRhamComplex (A := A) δ).differential n) := by
  apply LinearMap.ext_on_range
    (exactForms_span (R := A) _ (dividedPowerDifferentials_span δ) n)
  intro b
  change (dividedPowerDeRhamComplex (A := A) ε).differential n
    (dpFormsMap (A := A) δ ε h n _) =
    dpFormsMap (A := A) δ ε h (n + 1)
      ((dividedPowerDeRhamComplex (A := A) δ).differential n _)
  rw [dpFormsMap_generator, dividedPowerDeRhamComplex_differential_generator]
  calc
    _ = exteriorPower.ιMulti C (n + 1)
        (fun j => dividedPowerDifferential (A := A) ε (algebraMap B C (b j))) :=
      (dividedPowerDeRhamComplex (A := A) ε).differential_generator n
        (fun j => algebraMap B C (b j))
    _ = _ := by
      rw [dpFormsMap, exteriorPowerMap_ιMulti]
      simp only [dpDifferentialsMap_d]


private def dpFormsQuotientEquiv
    (hs : Function.Surjective (algebraMap B C))
    (L : Ideal B) (hL : L = RingHom.ker (algebraMap B C))
    (E : (dividedPowerDifferentials (A := A) δ ⧸
      L • (⊤ : Submodule B (dividedPowerDifferentials (A := A) δ))) ≃+
        dividedPowerDifferentials (A := A) ε)
    (hE : ∀ x, E (Submodule.Quotient.mk x) = dpDifferentialsMap (A := A) δ ε h x)
    (n : ℕ) :
    { F : (dividedPowerDifferentialForms (A := A) δ n ⧸
      L • (⊤ : Submodule B (dividedPowerDifferentialForms (A := A) δ n))) ≃ₗ[B]
        dividedPowerDifferentialForms (A := A) ε n //
      ∀ x, F (Submodule.Quotient.mk x) = dpFormsMap (A := A) δ ε h n x } := by
  let EL : (dividedPowerDifferentials (A := A) δ ⧸
      L • (⊤ : Submodule B (dividedPowerDifferentials (A := A) δ))) ≃ₗ[B]
        dividedPowerDifferentials (A := A) ε :=
    { E with
      map_smul' := by
        intro b x
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
        change E (Submodule.Quotient.mk (b • x)) = b • E (Submodule.Quotient.mk x)
        rw [hE, hE, map_smul] }
  have hf := isBaseChange_of_quotientEquiv (dpDifferentialsMap (A := A) δ ε h)
    hs L hL EL hE
  exact quotientEquivOfIsBaseChange (dpFormsMap (A := A) δ ε h n) hs L hL
    (DeRhamBaseChange.isBaseChange_exteriorPower hf _ (exteriorPowerMap_ιMulti _ n))

end Maps

private theorem pAdicPowSMul_restrictScalars
    {R S X : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup X] [mR : Module R X] [mS : Module S X] [tRS : IsScalarTower R S X]
    (p n : ℕ) :
    (pAdicIdeal (A := S) p ^ n • (⊤ : Submodule S X)).restrictScalars R =
      pAdicIdeal (A := R) p ^ n • (⊤ : Submodule R X) := by
  ext x
  simp only [pAdicIdeal, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul, Submodule.restrictScalars_mem,
    Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  have he (y : X) : (p : S) ^ n • y = (p : R) ^ n • y := by
    rw [← IsScalarTower.algebraMap_smul S ((p : R) ^ n) y]
    simp only [map_pow, map_natCast]
  simp only [he]

/-- **A linear map bijective at every level of the `I`-adic filtration is bijective on the
`I`-adic completions.**  Injectivity is checked level by level, two elements of a completion
agreeing at every level being equal; surjectivity lifts a compatible family through the levelwise
inverses, and the lifts are compatible because they are unique.

Mathlib has no `AdicCompletion.map_bijective`.  The statement is what identifies a completion
built one way with a completion built another whenever the two agree modulo every `I ^ n`. -/
public theorem completionMap_bijective_of_reduceModIdeal
    {R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (I : Ideal R) (f : X →ₗ[R] Y)
    (hf : ∀ n : ℕ, Function.Bijective (f.reduceModIdeal (I ^ n))) :
    Function.Bijective (AdicCompletion.map I f) := by
  constructor
  · intro x y hxy
    apply AdicCompletion.ext
    intro n
    apply (hf n).injective
    exact congrArg (fun z : AdicCompletion I Y => z.val n) hxy
  · intro y
    choose x hx using fun n => (hf n).surjective (y.val n)
    have hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
        AdicCompletion.transitionMap I X hmn (x n) = x m := by
      intro m n hmn
      apply (hf m).injective
      have ht := LinearMap.congr_fun
        (AdicCompletion.transitionMap_comp_reduceModIdeal I f hmn) (x n)
      change AdicCompletion.transitionMap I Y hmn (f.reduceModIdeal (I ^ n) (x n)) =
        f.reduceModIdeal (I ^ m) (AdicCompletion.transitionMap I X hmn (x n)) at ht
      rw [← ht, hx, y.property, hx]
    exact ⟨⟨x, hcompat⟩, AdicCompletion.ext hx⟩

private theorem completion_linearMap_ext
    {R X Y : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup Y] [Module R Y] (I : Ideal R) (hI : I.FG) [IsHausdorff I Y]
    {f g : AdicCompletion I X →ₗ[R] Y}
    (h : ∀ x, f (AdicCompletion.of I X x) = g (AdicCompletion.of I X x)) : f = g := by
  apply LinearMap.ext
  intro x
  apply eq_of_sub_eq_zero
  apply (inferInstance : IsHausdorff I Y).haus
  intro n
  obtain ⟨a, ha⟩ := Submodule.mkQ_surjective (I ^ n • (⊤ : Submodule R X)) (x.val n)
  have hx : x - AdicCompletion.of I X a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I X)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI]
    change AdicCompletion.eval I X n (x - AdicCompletion.of I X a) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr ha.symm
  have hmem (k : AdicCompletion I X →ₗ[R] Y) : k (x - AdicCompletion.of I X a) ∈
      I ^ n • (⊤ : Submodule R Y) := by
    have H := Submodule.mem_map_of_mem (f := k) hx
    rw [Submodule.map_smul''] at H
    exact (show I ^ n • Submodule.map k ⊤ ≤ I ^ n • (⊤ : Submodule R Y) from
      smul_mono_right _ le_top) H
  apply SModEq.zero.mpr
  have H := (I ^ n • (⊤ : Submodule R Y)).sub_mem (hmem f) (hmem g)
  simpa only [map_sub, h, sub_sub_sub_cancel_right] using H


private def dpFormsModPowEquiv
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    {J : Ideal B} {K : Ideal C} (δ : DividedPowers J) (ε : DividedPowers K)
    (h : δ.IsDPMorphism ε (algebraMap B C))
    (hs : Function.Surjective (algebraMap B C)) (p e n : ℕ)
    [mA : Module A (dividedPowerDifferentialForms (A := A) δ n)]
    [tAB : @IsScalarTower A B (dividedPowerDifferentialForms (A := A) δ n)
      inferInstance inferInstance mA.toSMul]
    [mC : Module A (dividedPowerDifferentialForms (A := A) ε n)]
    [tAC : @IsScalarTower A C (dividedPowerDifferentialForms (A := A) ε n)
      inferInstance inferInstance mC.toSMul]
    (hker : pAdicIdeal (A := B) p ^ e = RingHom.ker (algebraMap B C))
    (E : (dividedPowerDifferentials (A := A) δ ⧸
      pAdicIdeal (A := B) p ^ e •
        (⊤ : Submodule B (dividedPowerDifferentials (A := A) δ))) ≃+
        dividedPowerDifferentials (A := A) ε)
    (hE : ∀ x, E (Submodule.Quotient.mk x) = dpDifferentialsMap (A := A) δ ε h x) :
    { F : ((dividedPowerDifferentialForms (A := A) δ n) ⧸
      pAdicIdeal (A := A) p ^ e •
        (⊤ : Submodule A ((dividedPowerDifferentialForms (A := A) δ n)))) ≃ₗ[A]
        (dividedPowerDifferentialForms (A := A) ε n) //
      ∀ b : Fin (n + 1) → B,
        F (Submodule.Quotient.mk
          (b 0 • exteriorPower.ιMulti B n
            (fun j => dividedPowerDifferential (A := A) δ (b j.succ)))) =
        algebraMap B C (b 0) • exteriorPower.ιMulti C n
          (fun j => dividedPowerDifferential (A := A) ε (algebraMap B C (b j.succ))) } := by
  letI : SMul A (dividedPowerDifferentialForms (A := A) δ n) := mA.toSMul
  letI : SMul A (dividedPowerDifferentialForms (A := A) ε n) := mC.toSMul
  letI : IsScalarTower A B (dividedPowerDifferentialForms (A := A) ε n) :=
    IsScalarTower.of_algebraMap_smul (fun a x => by
      rw [← IsScalarTower.algebraMap_smul C (algebraMap A B a) x,
        ← IsScalarTower.algebraMap_apply A B C, IsScalarTower.algebraMap_smul C])
  let F := dpFormsQuotientEquiv (A := A) δ ε h hs _ hker E hE n
  let q := Submodule.quotEquivOfEq _ _
    (pAdicPowSMul_restrictScalars (R := A) (S := B)
      (X := dividedPowerDifferentialForms (A := A) δ n) (mR := mA)
      (mS := inferInstanceAs (Module B (dividedPowerDifferentialForms (A := A) δ n)))
      (tRS := tAB) p e)
  refine ⟨q.symm.trans ((Submodule.Quotient.restrictScalarsEquiv A
      (pAdicIdeal (A := B) p ^ e •
        (⊤ : Submodule B (dividedPowerDifferentialForms (A := A) δ n)))).trans
    (F.val.restrictScalars A)), ?_⟩
  intro b
  change F.val (Submodule.Quotient.mk _) = _
  rw [F.property]
  exact dpFormsMap_generator δ ε h n b



private theorem toCompletedRing_isDPMorphism :
    (canonicalDividedPowers A W).IsDPMorphism cdp.dividedPowers
      (toCompletedRing p A W) where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr fun x hx =>
    toCompletedRing_mem_augmentationIdeal p A W x hx
  dpow_comp := by
    intro n x hx
    exact (cdp.dpow_toCompletedRing n x hx
      ⟨_, toCompletedRing_mem_augmentationIdeal p A W x hx⟩ rfl)

private abbrev polynomialForms (n : ℕ) :=
  (augmentedDividedPowerDeRhamTerm A W (n + 1) : Type (max uA uW))

private abbrev polynomialDeRhamDifferential (n : ℕ) :
    polynomialForms A W n →ₗ[A] polynomialForms A W (n + 1) :=
  (augmentedDividedPowerDeRhamDifferential A W (n + 1)).hom

private def polynomialFormsMap (n : ℕ) :
    polynomialForms A W n →ₗ[A] forms p A W cdp n := by
  letI : Module (dividedPowerPolynomialRing A W)
      (dividedPowerDifferentialForms (A := A) cdp.dividedPowers n) :=
    Module.restrictScalars (dividedPowerPolynomialRing A W) (completedRing p A W) _
  exact (dpFormsMap (A := A) (canonicalDividedPowers A W) cdp.dividedPowers
    (toCompletedRing_isDPMorphism p A W cdp) n).restrictScalars A

private def polynomialFormsModPowEquiv (e n : ℕ) :
    { F : (polynomialForms A W n ⧸
      pAdicIdeal (A := A) p ^ e • (⊤ : Submodule A _)) ≃ₗ[A]
      RestrictScalars A (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e)
        (dividedPowerDifferentialForms (A := A) (quotientAugmentationDividedPowers p A W e) n) //
      ∀ b : Fin (n + 1) → dividedPowerPolynomialRing A W,
        F (Submodule.Quotient.mk
          (b 0 • exteriorPower.ιMulti _ n (fun j => dividedPowerDifferential (A := A)
            (canonicalDividedPowers A W) (b j.succ)))) =
        Ideal.Quotient.mk (pAdicIdeal (A := dividedPowerPolynomialRing A W) p ^ e) (b 0) •
          exteriorPower.ιMulti _ n
            (fun j => dividedPowerDifferential (A := A)
              (quotientAugmentationDividedPowers p A W e)
              (Ideal.Quotient.mk
                (pAdicIdeal (A := dividedPowerPolynomialRing A W) p ^ e)
                (b j.succ))) } := by
  letI : Module A
      (dividedPowerDifferentialForms (A := A) (canonicalDividedPowers A W) n) :=
    Module.restrictScalars A (dividedPowerPolynomialRing A W) _
  letI : IsScalarTower A (dividedPowerPolynomialRing A W)
      (dividedPowerDifferentialForms (A := A) (canonicalDividedPowers A W) n) :=
    IsScalarTower.restrictScalars A (dividedPowerPolynomialRing A W) _
  letI : Module A
      (dividedPowerDifferentialForms (A := A)
        (quotientAugmentationDividedPowers p A W e) n) :=
    Module.restrictScalars A (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e) _
  letI : IsScalarTower A (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e)
      (dividedPowerDifferentialForms (A := A)
        (quotientAugmentationDividedPowers p A W e) n) :=
    IsScalarTower.restrictScalars A (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e) _
  let E := differentialsQuotientInfEquiv (A := A) (augmentationIdeal A W)
    (canonicalDividedPowers A W) (pAdicIdeal p ^ e)
    (augmentationIdeal_inf_isSubDPIdeal p A W e)
    (fun x hx => dividedPowerDifferential_mem_pAdicPow _
      (canonicalDividedPowers A W) p e hx)
  apply dpFormsModPowEquiv (canonicalDividedPowers A W)
    (quotientAugmentationDividedPowers p A W e)
    (DividedPowers.Quotient.isDPMorphism _ _) Ideal.Quotient.mk_surjective p e n
    (tAB := IsScalarTower.restrictScalars A (dividedPowerPolynomialRing A W) _)
    (tAC := IsScalarTower.restrictScalars A
      (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e) _)
    (Ideal.mk_ker.symm) E.val.toAddEquiv
  intro x
  exact differentialsQuotientInfEquiv_mk (A := A) (augmentationIdeal A W)
    (canonicalDividedPowers A W) (pAdicIdeal p ^ e)
    (augmentationIdeal_inf_isSubDPIdeal p A W e)
    (fun b hb => dividedPowerDifferential_mem_pAdicPow _
      (canonicalDividedPowers A W) p e hb) x

private def completedFormsModPowEquiv (e n : ℕ) :
    { F : (forms p A W cdp n ⧸
      pAdicIdeal (A := A) p ^ e • (⊤ : Submodule A _)) ≃ₗ[A]
      RestrictScalars A (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e)
        (dividedPowerDifferentialForms (A := A) (quotientAugmentationDividedPowers p A W e) n) //
      ∀ b : Fin (n + 1) → completedRing p A W,
        F (Submodule.Quotient.mk
          (b 0 • exteriorPower.ιMulti _ n (fun j => dividedPowerDifferential (A := A)
            cdp.dividedPowers (b j.succ)))) =
        AdicCompletion.evalₐ (pAdicIdeal p) e (b 0) • exteriorPower.ιMulti _ n
          (fun j => dividedPowerDifferential (A := A)
            (quotientAugmentationDividedPowers p A W e)
            (AdicCompletion.evalₐ (pAdicIdeal p) e (b j.succ))) } := by
  let f := (AdicCompletion.evalₐ
    (pAdicIdeal (A := dividedPowerPolynomialRing A W) p) e).restrictScalars A
  letI : Algebra (completedRing p A W)
      (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e) := f.toRingHom.toAlgebra
  letI : IsScalarTower A (completedRing p A W)
      (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e) :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  letI : Module A (dividedPowerDifferentialForms (A := A) (cdp.dividedPowers) n) :=
    Module.restrictScalars A (completedRing p A W) _
  letI : IsScalarTower A (completedRing p A W)
      (dividedPowerDifferentialForms (A := A) (cdp.dividedPowers) n) :=
    IsScalarTower.restrictScalars A (completedRing p A W) _
  letI : Module A
      (dividedPowerDifferentialForms (A := A)
        (quotientAugmentationDividedPowers p A W e) n) :=
    Module.restrictScalars A (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e) _
  letI : IsScalarTower A (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e)
      (dividedPowerDifferentialForms (A := A)
        (quotientAugmentationDividedPowers p A W e) n) :=
    IsScalarTower.restrictScalars A (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e) _
  let E := completedDifferentialsModPowEquiv p A W cdp e
  apply dpFormsModPowEquiv cdp.dividedPowers
    (quotientAugmentationDividedPowers p A W e) (eval_isDPMorphism p A W cdp e)
    (AdicCompletion.surjective_evalₐ _ e) p e n
    (tAB := IsScalarTower.restrictScalars A (completedRing p A W) _)
    (tAC := IsScalarTower.restrictScalars A
      (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e) _)
    (completedRing_pAdicPow_eq_ker_eval p A W e) E.val
  intro x
  exact E.property x

private theorem polynomialFormsMap_reduce_bijective (e n : ℕ) :
    Function.Bijective ((polynomialFormsMap p A W cdp n).reduceModIdeal
      (pAdicIdeal (A := A) p ^ e)) := by
  let : Module A (RestrictScalars A
      (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e)
      (dividedPowerDifferentialForms (A := A)
        (quotientAugmentationDividedPowers p A W e) n)) :=
    RestrictScalars.module A
      (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e)
      (dividedPowerDifferentialForms (A := A)
        (quotientAugmentationDividedPowers p A W e) n)
  let E := polynomialFormsModPowEquiv p A W e n
  let F := completedFormsModPowEquiv p A W cdp e n
  let g := ((polynomialFormsMap p A W cdp n).reduceModIdeal
    (pAdicIdeal (A := A) p ^ e)).restrictScalars A
  have hg : F.val.toLinearMap.comp g = E.val.toLinearMap := by
    apply Submodule.linearMap_qext (R := A) (R₂ := A)
      (M := polynomialForms A W n)
      (M₂ := RestrictScalars A
        (dividedPowerPolynomialRing A W ⧸ pAdicIdeal p ^ e)
        (dividedPowerDifferentialForms (A := A)
          (quotientAugmentationDividedPowers p A W e) n))
      (pAdicIdeal (A := A) p ^ e • (⊤ : Submodule A (polynomialForms A W n)))
    apply LinearMap.ext_on_range (exactForms_span (R := A) _
      (dividedPowerDifferentials_span (canonicalDividedPowers A W)) n)
    intro b
    change F.val (Submodule.Quotient.mk (polynomialFormsMap p A W cdp n
      (b 0 • exteriorPower.ιMulti _ n (fun j => dividedPowerDifferential (A := A)
        (canonicalDividedPowers A W) (b j.succ))))) = E.val (Submodule.Quotient.mk _)
    have hgen := dpFormsMap_generator (A := A) (canonicalDividedPowers A W)
      cdp.dividedPowers (toCompletedRing_isDPMorphism p A W cdp) n b
    exact (congrArg
      (fun x : forms p A W cdp n => F.val (Submodule.Quotient.mk x)) hgen).trans
        ((F.property (fun j => toCompletedRing p A W (b j))).trans (E.property b).symm)
  have hg' : g = F.val.symm.toLinearMap.comp E.val.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply F.val.injective
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      using LinearMap.congr_fun hg x
  change Function.Bijective g
  rw [hg']
  exact F.val.symm.bijective.comp E.val.bijective

private def completedPolynomialFormsEquiv (n : ℕ) :
    AdicCompletion (pAdicIdeal (A := A) p) (polynomialForms A W n) ≃ₗ[A]
      completedForms p A W cdp n :=
  LinearEquiv.ofBijective
    ((AdicCompletion.map (pAdicIdeal (A := A) p)
      (polynomialFormsMap p A W cdp n)).restrictScalars A)
    (completionMap_bijective_of_reduceModIdeal _ _
      (fun e => polynomialFormsMap_reduce_bijective p A W cdp e n))


private theorem completedTensor_complete_exact_of_contractible
    {R : Type*} [CommRing R] (I : Ideal R)
    (C : CochainComplex (ModuleCat.{uW} R) ℕ)
    (h : Homotopy (CategoryTheory.CategoryStruct.id C) 0)
    (N : Type*) [AddCommGroup N] [Module R N] (n : ℕ) :
    Function.Exact
      (AdicCompletion.map I
        (((AdicCompletion.map I (C.d n (n + 1)).hom).restrictScalars R).lTensor N))
      (AdicCompletion.map I
        (((AdicCompletion.map I
          (C.d (n + 1) (n + 1 + 1)).hom).restrictScalars R).lTensor N)) := by
  let s := (h.hom (n + 1) n).hom
  let t := (h.hom (n + 1 + 1) (n + 1)).hom
  have hgf : (C.d (n + 1) (n + 1 + 1)).hom.comp (C.d n (n + 1)).hom = 0 :=
    congrArg ModuleCat.Hom.hom (C.d_comp_d n (n + 1) (n + 1 + 1))
  have hs : (C.d n (n + 1)).hom.comp s + t.comp (C.d (n + 1) (n + 1 + 1)).hom = LinearMap.id := by
    have hc := h.comm (n + 1)
    rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel (n + 1) (n + 1 + 1) from rfl),
      prevD_eq _ (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)] at hc
    have H := congrArg ModuleCat.Hom.hom hc
    simpa only [HomologicalComplex.id_f, HomologicalComplex.zero_f,
      ModuleCat.hom_id, ModuleCat.hom_add, ModuleCat.hom_comp, ModuleCat.hom_zero,
      add_zero, zero_add, add_comm] using H.symm
  apply completedTensor_exact_of_splitting I _ _
    ((AdicCompletion.map I s).restrictScalars R) ((AdicCompletion.map I t).restrictScalars R)
  · apply LinearMap.ext
    intro x
    change AdicCompletion.map I _ (AdicCompletion.map I _ x) = 0
    rw [AdicCompletion.map_comp_apply, hgf, AdicCompletion.map_zero, LinearMap.zero_apply]
  · apply LinearMap.ext
    intro x
    have H := congrArg (fun f => AdicCompletion.map I f x) hs
    simpa only [map_add, LinearMap.add_apply, ← AdicCompletion.map_comp_apply,
      AdicCompletion.map_id, LinearMap.id_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply] using H

private theorem exact_of_linearEquiv
    {R X Y Z X' Y' Z' : Type*} [CommRing R]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    [AddCommGroup Z] [Module R Z] [AddCommGroup X'] [Module R X']
    [AddCommGroup Y'] [Module R Y'] [AddCommGroup Z'] [Module R Z']
    (eX : X ≃ₗ[R] X') (eY : Y ≃ₗ[R] Y') (eZ : Z ≃ₗ[R] Z')
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (f' : X' →ₗ[R] Y') (g' : Y' →ₗ[R] Z')
    (h : Function.Exact f g)
    (hf : ∀ x, f' (eX x) = eY (f x))
    (hg : ∀ y, g' (eY y) = eZ (g y)) : Function.Exact f' g' := by
  intro y'
  obtain ⟨y, rfl⟩ := eY.surjective y'
  constructor
  · intro hy
    have hy' : g y = 0 := eZ.injective (by rw [map_zero, ← hg]; exact hy)
    obtain ⟨x, hx⟩ := (h y).mp hy'
    exact ⟨eX x, by rw [hf, hx]⟩
  · rintro ⟨x', hx⟩
    obtain ⟨x, rfl⟩ := eX.surjective x'
    have hx' : f x = y := eY.injective ((hf x).symm.trans hx)
    rw [hg, (h y).mpr ⟨x, hx'⟩, map_zero]

private theorem completedPolynomialFormsEquiv_comm (n : ℕ) :
    (completedDeRhamDifferential p A W cdp n).comp
        (completedPolynomialFormsEquiv p A W cdp n).toLinearMap =
      (completedPolynomialFormsEquiv p A W cdp (n + 1)).toLinearMap.comp
        ((AdicCompletion.map (pAdicIdeal (A := A) p)
          (polynomialDeRhamDifferential A W n)).restrictScalars A) := by
  have H := dpFormsMap_comm (A := A) (canonicalDividedPowers A W) cdp.dividedPowers
    (toCompletedRing_isDPMorphism p A W cdp) n
  apply LinearMap.ext
  intro x
  change AdicCompletion.map (pAdicIdeal p) _
      (AdicCompletion.map (pAdicIdeal p) _ x) =
    AdicCompletion.map (pAdicIdeal p) _
      (AdicCompletion.map (pAdicIdeal p) _ x)
  rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply]
  exact congrArg (fun f => AdicCompletion.map (pAdicIdeal p) f x) H

private def completedTensorFormsEquiv (n : ℕ) :
    AdicCompletion (pAdicIdeal (A := A) p)
      (M ⊗[A] AdicCompletion (pAdicIdeal (A := A) p) (polynomialForms A W n)) ≃ₗ[A]
      completedTensorForms p A W cdp M n :=
  (AdicCompletion.congr (pAdicIdeal (A := A) p)
    ((completedPolynomialFormsEquiv p A W cdp n).lTensor M)).restrictScalars A

private def completedPolynomialTensorDifferential (n : ℕ) :
    AdicCompletion (pAdicIdeal (A := A) p)
      (M ⊗[A] AdicCompletion (pAdicIdeal (A := A) p) (polynomialForms A W n)) →ₗ[A]
    AdicCompletion (pAdicIdeal (A := A) p)
      (M ⊗[A] AdicCompletion (pAdicIdeal (A := A) p) (polynomialForms A W (n + 1))) :=
  (AdicCompletion.map (pAdicIdeal (A := A) p)
    (((AdicCompletion.map (pAdicIdeal (A := A) p)
      (polynomialDeRhamDifferential A W n)).restrictScalars A).lTensor M)).restrictScalars A

private theorem completedTensorFormsEquiv_comm (n : ℕ) (x) :
    differential p A W cdp M n (completedTensorFormsEquiv p A W cdp M n x) =
      completedTensorFormsEquiv p A W cdp M (n + 1)
        (completedPolynomialTensorDifferential p A W M n x) := by
  change AdicCompletion.map (pAdicIdeal p) _
      (AdicCompletion.map (pAdicIdeal p) _ x) =
    AdicCompletion.map (pAdicIdeal p) _
      (AdicCompletion.map (pAdicIdeal p) _ x)
  rw [AdicCompletion.map_comp_apply, AdicCompletion.map_comp_apply]
  apply congrArg (fun f => AdicCompletion.map (pAdicIdeal p) f x)
  change ((completedDeRhamDifferential p A W cdp n).lTensor M).comp
      (((completedPolynomialFormsEquiv p A W cdp n).toLinearMap).lTensor M) = _
  rw [← LinearMap.lTensor_comp, completedPolynomialFormsEquiv_comm, LinearMap.lTensor_comp]
  rfl

private theorem completedTensorForms_exact (i : ℕ) :
    Function.Exact (differential p A W cdp M i)
      (differential p A W cdp M (i + 1)) := by
  obtain ⟨h⟩ := augmentedDividedPowerDeRhamComplex_contractible A W
  have H := completedTensor_complete_exact_of_contractible
    (pAdicIdeal (A := A) p) _ h M (i + 1)
  simp only [augmentedDividedPowerDeRhamComplex, CochainComplex.of_d] at H
  apply exact_of_linearEquiv (completedTensorFormsEquiv p A W cdp M i)
    (completedTensorFormsEquiv p A W cdp M (i + 1))
    (completedTensorFormsEquiv p A W cdp M (i + 1 + 1))
    (completedPolynomialTensorDifferential p A W M i)
    (completedPolynomialTensorDifferential p A W M (i + 1)) _ _ H
    (completedTensorFormsEquiv_comm p A W cdp M i)
    (completedTensorFormsEquiv_comm p A W cdp M (i + 1))

private theorem completedTensor_linearMap_ext
    {R N X Y : Type*} [CommRing R] [AddCommGroup N] [Module R N]
    [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (I : Ideal R) (hI : I.FG) [IsHausdorff I Y]
    {f g : AdicCompletion I (N ⊗[R] AdicCompletion I X) →ₗ[R] Y}
    (h : ∀ n x, f (AdicCompletion.of I _ (n ⊗ₜ[R] AdicCompletion.of I X x)) =
      g (AdicCompletion.of I _ (n ⊗ₜ[R] AdicCompletion.of I X x))) : f = g := by
  apply completion_linearMap_ext I hI
  have H : f.comp (AdicCompletion.of I _) = g.comp (AdicCompletion.of I _) := by
    apply TensorProduct.ext'
    intro n
    have Hn :
        (f.comp (AdicCompletion.of I _)).comp (TensorProduct.mk R N _ n) =
          (g.comp (AdicCompletion.of I _)).comp (TensorProduct.mk R N _ n) := by
      apply completion_linearMap_ext I hI
      exact h n
    exact LinearMap.congr_fun Hn
  exact LinearMap.congr_fun H

private abbrev polynomialCoefficients :=
  (augmentedDividedPowerDeRhamTerm A W 0 : Type (max uA uW))

private def completedPolynomialTensorAugmentation :
    AdicCompletion (pAdicIdeal (A := A) p)
      (M ⊗[A] AdicCompletion (pAdicIdeal (A := A) p)
        (polynomialCoefficients A W)) →ₗ[A]
      AdicCompletion (pAdicIdeal (A := A) p)
        (M ⊗[A] AdicCompletion (pAdicIdeal (A := A) p)
          (polynomialForms A W 0)) :=
  (AdicCompletion.map (pAdicIdeal (A := A) p)
    (((AdicCompletion.map (pAdicIdeal (A := A) p)
      (augmentedDividedPowerDeRhamDifferential A W 0).hom).restrictScalars A).lTensor
        M)).restrictScalars A

private theorem polynomialFormsMap_coefficient (a : A) :
    polynomialFormsMap p A W cdp 0
      (augmentedDividedPowerDeRhamDifferential A W 0
        (coefficientLinearEquiv A W a)) =
      a • (exteriorPower.zeroEquiv (completedRing p A W)
        (differentials p A W cdp)).symm 1 := by
  let : Module (dividedPowerPolynomialRing A W)
      (dividedPowerDifferentials (A := A) cdp.dividedPowers) :=
    Module.restrictScalars (dividedPowerPolynomialRing A W) (completedRing p A W) _
  have h1 : polynomialFormsMap p A W cdp 0
      (augmentedDividedPowerDeRhamDifferential A W 0
        (coefficientLinearEquiv A W 1)) =
      (exteriorPower.zeroEquiv (completedRing p A W)
        (differentials p A W cdp)).symm 1 := by
    rw [augmentedDividedPowerDeRhamDifferential_coefficient, map_one]
    simp only [exteriorPower.zeroEquiv_symm_apply, one_smul]
    change dpFormsMap (A := A) _ _ _ 0 _ = _
    rw [dpFormsMap, exteriorPowerMap_ιMulti]
    congr 1
    funext i
    exact Fin.elim0 i
  let f : A →ₗ[A] forms p A W cdp 0 :=
    (polynomialFormsMap p A W cdp 0).comp
      ((augmentedDividedPowerDeRhamDifferential A W 0).hom.comp
        (coefficientLinearEquiv A W).toLinearMap)
  calc
    _ = f (a • (1 : A)) := by rw [smul_eq_mul, mul_one]; rfl
    _ = a • f 1 := f.map_smul a 1
    _ = _ := congrArg (a • ·) h1

private theorem completedPolynomialTensorAugmentation_coefficient (m : M) (a : A) :
    completedTensorFormsEquiv p A W cdp M 0
      (completedPolynomialTensorAugmentation p A W M
        (AdicCompletion.of (pAdicIdeal (A := A) p) _
          (m ⊗ₜ[A] AdicCompletion.of (pAdicIdeal (A := A) p)
            (polynomialCoefficients A W)
            (coefficientLinearEquiv A W a)))) =
      augmentation p A W cdp M (a • m) := by
  let I := pAdicIdeal (A := A) p
  let c : polynomialCoefficients A W := coefficientLinearEquiv A W a
  let z : forms p A W cdp 0 :=
    (exteriorPower.zeroEquiv (completedRing p A W) (differentials p A W cdp)).symm 1
  have hc : polynomialFormsMap p A W cdp 0
      ((augmentedDividedPowerDeRhamDifferential A W 0).hom c) = a • z :=
    polynomialFormsMap_coefficient p A W cdp a
  change AdicCompletion.map I _ (AdicCompletion.map I _
    (AdicCompletion.of I _ (m ⊗ₜ[A] AdicCompletion.of I (polynomialCoefficients A W) c))) = _
  rw [AdicCompletion.map_of, AdicCompletion.map_of]
  change AdicCompletion.of I _ (m ⊗ₜ[A]
    (AdicCompletion.map I (polynomialFormsMap p A W cdp 0)
      (AdicCompletion.map I _ (AdicCompletion.of I (polynomialCoefficients A W) c)))) = _
  rw [AdicCompletion.map_of, AdicCompletion.map_of, hc, map_smul]
  change AdicCompletion.of I _ (m ⊗ₜ[A] (a • AdicCompletion.of I _ z)) =
    AdicCompletion.of I _ ((a • m) ⊗ₜ[A] AdicCompletion.of I _ z)
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']

private theorem completedTensorForms_exact_augmentation
    (hM : IsAdicComplete (pAdicIdeal (A := A) p) M) :
    Function.Exact (augmentation p A W cdp M) (differential p A W cdp M 0) := by
  let I := pAdicIdeal (A := A) p
  let := hM
  let := AdicCompletion.isAdicComplete
    (M := M ⊗[A] completedForms p A W cdp 0) (pAdicIdeal_fg p A)
  let F := (completedTensorFormsEquiv p A W cdp M 0).toLinearMap.comp
    (completedPolynomialTensorAugmentation p A W M)
  let r := (AdicCompletion.ofLinearEquiv I M).symm.toLinearMap.comp
    (completedTensorAugmentationRetraction p A W cdp M)
  have hr (m : M) : r (augmentation p A W cdp M m) = m := by
    change (AdicCompletion.ofLinearEquiv I M).symm
      (completedTensorAugmentationRetraction p A W cdp M
        (augmentation p A W cdp M m)) = m
    rw [completedTensorAugmentationRetraction_augmentation,
      ← AdicCompletion.ofLinearEquiv_apply, LinearEquiv.symm_apply_apply]
  have hF : (augmentation p A W cdp M).comp (r.comp F) = F := by
    apply completedTensor_linearMap_ext I (pAdicIdeal_fg p A)
    intro m a
    obtain ⟨a, rfl⟩ := (coefficientLinearEquiv A W).surjective a
    change augmentation p A W cdp M (r (F _)) = F _
    change augmentation p A W cdp M
      (r (completedTensorFormsEquiv p A W cdp M 0
        (completedPolynomialTensorAugmentation p A W M _))) =
      completedTensorFormsEquiv p A W cdp M 0
        (completedPolynomialTensorAugmentation p A W M _)
    rw [completedPolynomialTensorAugmentation_coefficient, hr]
  obtain ⟨h⟩ := augmentedDividedPowerDeRhamComplex_contractible A W
  have H := completedTensor_complete_exact_of_contractible I _ h M 0
  simp only [augmentedDividedPowerDeRhamComplex, CochainComplex.of_d] at H
  change Function.Exact (completedPolynomialTensorAugmentation p A W M)
    (completedPolynomialTensorDifferential p A W M 0) at H
  intro y
  obtain ⟨z, rfl⟩ := (completedTensorFormsEquiv p A W cdp M 0).surjective y
  constructor
  · intro hy
    have hz : completedPolynomialTensorDifferential p A W M 0 z = 0 := by
      apply (completedTensorFormsEquiv p A W cdp M 1).injective
      rw [map_zero, ← completedTensorFormsEquiv_comm]
      exact hy
    obtain ⟨x, rfl⟩ := (H z).mp hz
    exact ⟨r (F x), LinearMap.congr_fun hF x⟩
  · rintro ⟨m, hm⟩
    let x := AdicCompletion.of I _
      (m ⊗ₜ[A] AdicCompletion.of I (polynomialCoefficients A W)
      (coefficientLinearEquiv A W 1))
    have hx : completedPolynomialTensorAugmentation p A W M x = z := by
      apply (completedTensorFormsEquiv p A W cdp M 0).injective
      calc
        _ = augmentation p A W cdp M (1 • m) :=
          completedPolynomialTensorAugmentation_coefficient p A W cdp M m 1
        _ = _ := by simpa only [one_smul] using hm
    rw [completedTensorFormsEquiv_comm, (H z).mpr ⟨x, hx⟩, map_zero]

/-- **Stacks Project, Tag 07LC, completed case.**  The first map `M → M ⊗̂_A D` of the
completed divided power de Rham complex of `P = A⟨x_w⟩` with coefficients in a `p`-adically
complete `A`-module `M` is injective. -/
@[stacks 07LC "completed_exactness"]
public theorem completedDeRham_tensor_augmentation_injective
    (hM : IsAdicComplete (pAdicIdeal (A := A) p) M) :
    Function.Injective (augmentation p A W (canonicalCompletedDividedPowers p A W) M) := by
  let := hM
  intro x y h
  apply (AdicCompletion.ofLinearEquiv (pAdicIdeal (A := A) p) M).injective
  have h' := congrArg (completedTensorAugmentationRetraction p A W
    (canonicalCompletedDividedPowers p A W) M) h
  simpa only [completedTensorAugmentationRetraction_augmentation,
    AdicCompletion.ofLinearEquiv_apply] using h'

/-- **Stacks Project, Tag 07LC, completed case.**  The completed divided power de Rham complex
of `P = A⟨x_w⟩` with coefficients in a `p`-adically complete `A`-module `M` is exact at
`M ⊗̂_A D`. -/
@[stacks 07LC "completed_exactness"]
public theorem completedDeRham_tensor_exact_augmentation
    (hM : IsAdicComplete (pAdicIdeal (A := A) p) M) :
    Function.Exact (augmentation p A W (canonicalCompletedDividedPowers p A W) M)
      (differential p A W (canonicalCompletedDividedPowers p A W) M 0) :=
  completedTensorForms_exact_augmentation p A W
    (canonicalCompletedDividedPowers p A W) M hM

/-- **Stacks Project, Tag 07LC, completed case.**  The completed divided power de Rham complex
of `P = A⟨x_w⟩` with coefficients in a `p`-adically complete `A`-module `M` is exact at
`M ⊗̂_A Ω^{i+1}_D` for every `i`. -/
@[stacks 07LC "completed_exactness"]
public theorem completedDeRham_tensor_exact
    (_hM : IsAdicComplete (pAdicIdeal (A := A) p) M) (i : ℕ) :
    Function.Exact (differential p A W (canonicalCompletedDividedPowers p A W) M i)
      (differential p A W (canonicalCompletedDividedPowers p A W) M (i + 1)) :=
  completedTensorForms_exact p A W (canonicalCompletedDividedPowers p A W) M i

end

end CompletedPoincare

end Crystalline

end
