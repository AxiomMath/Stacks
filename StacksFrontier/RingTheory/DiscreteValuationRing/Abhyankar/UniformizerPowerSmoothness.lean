module

public import StacksFrontier.RingTheory.DiscreteValuationRing.Abhyankar.RootUniformizerSmoothness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abhyankar's lemma: formal smoothness when the uniformizer is a power

Auxiliary results for Abhyankar's lemma: comparison of integral closures and their localizations
along fraction-field base changes, and formal smoothness of the local factors once the
uniformizer of the base is, up to a unit, a suitable power in the extension.

## Main results

* `IsDiscreteValuationRing.surjective_of_isLocalHom_of_isFractionRing`: a local homomorphism out
  of a valuation ring into a subring of its fraction field is surjective.

## References

* [The Stacks Project, Tag 0BRM](https://stacks.math.columbia.edu/tag/0BRM)
-/

@[expose] public section

namespace IsDiscreteValuationRing

section

universe u v w x y z

open scoped TensorProduct

open Polynomial

theorem isMaximal_comap_of_integral_square
    (A B C D : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A C] [Algebra B D] [Algebra.IsIntegral A C] [Algebra.IsIntegral B D]
    (g : C →+* D)
    (h : g.comp (algebraMap A C) = (algebraMap B D).comp (algebraMap A B))
    (q : Ideal D) [q.IsMaximal] : (q.comap g).IsMaximal := by
  have hp : (q.comap g).under A = IsLocalRing.maximalIdeal A := by
    show (q.comap g).comap (algebraMap A C) = _
    rw [Ideal.comap_comap, h, ← Ideal.comap_comap,
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal q),
      IsLocalRing.maximalIdeal_comap]
  apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) (q.comap g)
  show (Ideal.under A (q.comap g)).IsMaximal
  rw [hp]
  infer_instance

private theorem exists_tensorProduct_adjoinRoot_fieldFactor
    (K L : Type*) (E : Type u) [CommRing K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [Algebra L E] [IsScalarTower K L E]
    (f : K[X]) (x : E) (hx : f.eval₂ (algebraMap K E) x = 0) (hi : IsIntegral L x) :
    ∃ (F : Type u) (_ : Field F) (_ : Algebra L F) (_ : Algebra F E)
      (_ : IsScalarTower L F E),
      Module.Finite L F ∧ ∃ g : L ⊗[K] AdjoinRoot f →ₐ[L] F,
        Function.Surjective g ∧
        algebraMap F E (g (1 ⊗ₜ[K] AdjoinRoot.root f)) = x := by
  let F := IntermediateField.adjoin L {x}
  let xF : F := IntermediateField.AdjoinSimple.gen L x
  let : Module.Finite L F := IntermediateField.adjoin.finiteDimensional hi
  obtain ⟨e, he⟩ := exists_tensorProduct_adjoinRoot_equiv K L f
  have hxF : (f.map (algebraMap K L)).eval₂ (algebraMap L F) xF = 0 := by
    apply (algebraMap F E).injective
    rw [map_zero]
    show (IsScalarTower.toAlgHom L F E) (aeval xF (f.map (algebraMap K L))) = 0
    rw [← aeval_algHom_apply]
    show aeval x (f.map (algebraMap K L)) = 0
    rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq K L E]
    exact hx
  have hgen : Algebra.adjoin L {xF} = ⊤ := by
    simpa only [IntermediateField.adjoin.powerBasis_gen] using
      (IntermediateField.adjoin.powerBasis hi).adjoin_gen_eq_top
  let g : AdjoinRoot (f.map (algebraMap K L)) →ₐ[L] F :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId L F) xF hxF
  have hg : Function.Surjective g :=
    surjective_adjoinRoot_liftAlgHom_of_adjoin_eq_top _ xF hxF hgen
  refine ⟨F, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    g.comp e.toAlgHom, hg.comp e.surjective, ?_⟩
  show algebraMap F E (g (e (1 ⊗ₜ[K] AdjoinRoot.root f))) = x
  rw [he]
  exact congrArg (algebraMap F E) (AdjoinRoot.liftAlgHom_root _ _ _ _)

private theorem exists_integralClosure_ringEquiv_of_isIntegral
    (A C E : Type*) [CommRing A] [CommRing C] [CommRing E]
    [Algebra A C] [Algebra C E] [Algebra A E] [IsScalarTower A C E]
    [Algebra.IsIntegral A C] :
    ∃ e : integralClosure A E ≃+* integralClosure C E, ∀ a, (e a : E) = (a : E) :=
  ⟨{ toFun := fun a ↦ ⟨a, a.2.tower_top⟩
     invFun := fun a ↦ ⟨a, isIntegral_trans (R := A) (a : E) a.2⟩
     left_inv := fun _ ↦ rfl
     right_inv := fun _ ↦ rfl
     map_mul' := fun _ _ ↦ rfl
     map_add' := fun _ _ ↦ rfl }, fun _ ↦ rfl⟩

private theorem isLocalHom_algebraMap_of_isDiscreteValuationRing
    (A C D : Type*) [CommRing A] [IsLocalRing A] [CommRing C] [IsDomain C]
    [IsDiscreteValuationRing C] [CommRing D] [IsLocalRing D]
    [Algebra A C] [Algebra C D] [Algebra A D] [IsScalarTower A C D]
    [IsLocalHom (algebraMap A D)] (a : A) (ha : a ∈ IsLocalRing.maximalIdeal A)
    (ha0 : algebraMap A C a ≠ 0) : IsLocalHom (algebraMap C D) := by
  apply ((IsLocalRing.local_hom_TFAE (algebraMap C D)).out 5 1).mp
  have hne : (IsLocalRing.maximalIdeal D).comap (algebraMap C D) ≠ ⊥ := by
    intro h
    apply ha0
    have hmem : algebraMap A C a ∈ (IsLocalRing.maximalIdeal D).comap (algebraMap C D) := by
      rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
      exact map_nonunit _ a ha
    rw [h] at hmem
    exact (Submodule.mem_bot C).mp hmem
  exact IsLocalRing.eq_maximalIdeal (Ideal.IsPrime.isMaximal inferInstance hne)

/-- Let `R` be a valuation ring with fraction field `K` and let `R → S` be a local homomorphism
into a ring `S` that maps injectively into `K` over `R`. Then `R → S` is surjective: every element
of `S` is already a unit times an integer of `R`, since `K` is the fraction field of `R`. -/
theorem surjective_of_isLocalHom_of_isFractionRing
    (R S K : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing S] [Field K] [Algebra R S] [Algebra R K] [Algebra S K]
    [IsFractionRing R K] [IsScalarTower R S K]
    [IsLocalHom (algebraMap R S)]
    (hS : Function.Injective (algebraMap S K)) :
    Function.Surjective (algebraMap R S) := by
  intro x
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  have hxK : algebraMap S K x ≠ 0 := by simpa using hS.ne hx
  rcases ValuationRing.isInteger_or_isInteger R (algebraMap S K x) with
    ⟨a, ha⟩ | ⟨a, ha⟩
  · exact ⟨a, hS (by rw [← IsScalarTower.algebraMap_apply R S K, ha])⟩
  have hamul : algebraMap R S a * x = 1 := by
    apply hS
    rw [map_mul, ← IsScalarTower.algebraMap_apply R S K, ha, inv_mul_cancel₀ hxK, map_one]
  have hau : IsUnit a := isUnit_of_map_unit (algebraMap R S) a
    (IsUnit.of_mul_eq_one _ hamul)
  obtain ⟨u, rfl⟩ := hau
  refine ⟨↑u⁻¹, ?_⟩
  have h := congrArg (fun z => algebraMap R S (↑u⁻¹) * z) hamul
  simpa [← mul_assoc, ← map_mul] using h.symm

private theorem exists_integralClosure_hom_to_integrallyClosed
    (A S E : Type*) [CommRing A] [CommRing S] [IsDomain S]
    [IsIntegrallyClosed S] [Field E] [Algebra A S] [Algebra A E] [Algebra S E]
    [IsScalarTower A S E] [IsFractionRing S E] :
    ∃ f : integralClosure A E →ₐ[A] S,
      ∀ x, algebraMap S E (f x) = (x : E) := by
  classical
  have hex (x : integralClosure A E) : ∃ s : S, algebraMap S E s = (x : E) :=
    IsIntegrallyClosed.algebraMap_eq_of_integral x.2.tower_top
  let f : integralClosure A E → S := fun x ↦ (hex x).choose
  have hf (x) : algebraMap S E (f x) = (x : E) := (hex x).choose_spec
  refine ⟨{ toFun := f
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_
            commutes' := ?_ }, hf⟩
  · apply IsFractionRing.injective S E
    simp only [hf, map_one, OneMemClass.coe_one]
  · intro x y
    apply IsFractionRing.injective S E
    simp only [hf, map_mul, MulMemClass.coe_mul]
  · apply IsFractionRing.injective S E
    simp only [hf, map_zero, ZeroMemClass.coe_zero]
  · intro x y
    apply IsFractionRing.injective S E
    simp only [hf, map_add, AddMemClass.coe_add]
  · intro a
    apply IsFractionRing.injective S E
    rw [hf, ← IsScalarTower.algebraMap_apply]
    rfl

private theorem exists_injective_localizationAtPrime_lift
    {C T : Type*} [CommRing C] [IsDomain C] [CommRing T] [IsLocalRing T]
    (f : C →+* T) (hf : Function.Injective f) (q : Ideal C) [q.IsPrime]
    (hq : q = (IsLocalRing.maximalIdeal T).comap f) :
    ∃ g : Localization.AtPrime q →+* T,
      Function.Injective g ∧ IsLocalHom g ∧ ∀ c, g (algebraMap C _ c) = f c := by
  classical
  have hu (m : q.primeCompl) : IsUnit (f m) := by
    apply not_not.mp
    intro hn
    exact m.2 (hq.ge hn)
  let g : Localization.AtPrime q →+* T := IsLocalization.lift hu
  have hg (c : C) : g (algebraMap C _ c) = f c := IsLocalization.lift_eq hu c
  refine ⟨g, ?_, ?_, hg⟩
  · apply (IsLocalization.lift_injective_iff hu).mpr
    intro a b
    rw [(IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors).eq_iff,
      hf.eq_iff]
  · constructor
    intro t ht
    obtain ⟨r, m, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl t
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    have heq : g (IsLocalization.mk' (Localization.AtPrime q) r m) * f m = f r := by
      rw [← hg, ← map_mul, IsLocalization.mk'_spec, hg]
    have hunit : IsUnit (f r) := heq ▸ ht.mul (hu m)
    exact fun hr ↦ hq.le hr hunit

/-- For a DVR `A` and a local extension `S` of `A`, the preimage of the maximal ideal of `S`
under any `A`-algebra map into `S` is nonzero. -/
private theorem comap_maximalIdeal_ne_bot_of_algHom
    {A C S : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing C]
    [CommRing S] [IsDomain S] [IsLocalRing S] [Algebra A C] [Algebra A S]
    [FaithfulSMul A S] [IsLocalHom (algebraMap A S)]
    (f : C →ₐ[A] S) : (IsLocalRing.maximalIdeal S).comap f.toRingHom ≠ ⊥ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hm : algebraMap A C π ∈ (IsLocalRing.maximalIdeal S).comap f.toRingHom := by
    show f (algebraMap A C π) ∈ IsLocalRing.maximalIdeal S
    rw [f.commutes]
    exact map_nonunit _ π hπ.not_isUnit
  intro hp
  have hz : algebraMap A C π = 0 := by simpa only [hp, Submodule.mem_bot] using hm
  have hzS : algebraMap A S π = 0 := (f.commutes π).symm.trans ((congrArg f hz).trans (map_zero f))
  exact hπ.ne_zero ((FaithfulSMul.algebraMap_injective A S) (hzS.trans (map_zero _).symm))

private theorem exists_localizationAtPrime_equiv_of_fractionRing
    (R S K : Type*) [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDomain S] [IsLocalRing S] [Field K]
    [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
    [IsFractionRing R K] [IsFractionRing S K]
    (p : Ideal R) [p.IsPrime]
    (hp : p = (IsLocalRing.maximalIdeal S).comap (algebraMap R S)) (hp0 : p ≠ ⊥) :
    ∃ e : Localization.AtPrime p ≃ₐ[R] S,
      ∀ r, e (algebraMap R (Localization.AtPrime p) r) = algebraMap R S r := by
  classical
  let T := Localization.AtPrime p
  let : IsDiscreteValuationRing T :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hp0 T
  have hRS : Function.Injective (algebraMap R S) := by
    apply Function.Injective.of_comp (f := algebraMap S K)
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact IsFractionRing.injective R K
  obtain ⟨f, hinj, hloc, hf⟩ := exists_injective_localizationAtPrime_lift (algebraMap R S) hRS p hp
  obtain ⟨hTK, hRTK, hfrac⟩ := exists_fractionRing_localizationAtPrime_algebra R K p
  let := hTK
  let := hRTK
  let := hfrac
  let : Algebra T S := f.toAlgebra
  let : IsScalarTower T S K := .of_algebraMap_eq fun t ↦ by
    have heq : (algebraMap S K).comp f = algebraMap T K := by
      apply IsLocalization.ringHom_ext p.primeCompl
      ext r
      show algebraMap S K (f (algebraMap R T r)) =
        algebraMap T K (algebraMap R T r)
      rw [hf, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
    exact (RingHom.congr_fun heq t).symm
  have hsurj : Function.Surjective f := surjective_of_isLocalHom_of_isFractionRing T S K
    (IsFractionRing.injective S K)
  exact ⟨AlgEquiv.ofBijective { __ := f, commutes' := hf } ⟨hinj, hsurj⟩, hf⟩

private theorem exists_integralClosure_localization_equiv
    (A S K E : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Field E] [Algebra A S] [IsExtension A S]
    [Algebra A K] [IsFractionRing A K] [Algebra K E] [Module.Finite K E]
    [Algebra A E] [Algebra S E] [IsScalarTower A K E] [IsScalarTower A S E]
    [IsFractionRing S E] :
    ∃ (f : integralClosure A E →ₐ[A] S),
      (∀ x, algebraMap S E (f x) = (x : E)) ∧
      ∃ (p : Ideal (integralClosure A E)) (_ : p.IsMaximal),
        p = (IsLocalRing.maximalIdeal S).comap f.toRingHom ∧
        ∃ e : Localization.AtPrime p ≃+* S,
          ∀ x, e (algebraMap (integralClosure A E) _ x) = f x := by
  let C := integralClosure A E
  let : IsDedekindDomain C :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite A K E C).1
  let : IsFractionRing C E := integralClosure.isFractionRing_of_finite_extension K E
  obtain ⟨f, hf⟩ := exists_integralClosure_hom_to_integrallyClosed A S E
  let : Algebra C S := f.toAlgebra
  let : IsScalarTower C S E := .of_algebraMap_eq fun x ↦ (hf x).symm
  let p := (IsLocalRing.maximalIdeal S).comap f.toRingHom
  have hp0 : p ≠ ⊥ := comap_maximalIdeal_ne_bot_of_algHom f
  let : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp0
  obtain ⟨e, he⟩ := exists_localizationAtPrime_equiv_of_fractionRing C S E p rfl hp0
  exact ⟨f, hf, p, inferInstance, rfl, e.toRingEquiv, he⟩

set_option maxHeartbeats 800000 in
-- Elaborating the many nested localization and tensor-product algebra structures here is
-- expensive.
set_option synthInstance.maxHeartbeats 80000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem formallySmoothNAdic_of_fractionRing_baseChange
    (A : Type u) (B : Type v) (K L K₁ E S T : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Field L] [Field K₁] [Field E]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L]
    [Algebra K K₁] [Module.Finite K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [Algebra K E] [Algebra L E] [Algebra K₁ E] [Algebra B E]
    [IsScalarTower K L E] [IsScalarTower K K₁ E] [IsScalarTower B L E]
    [Algebra A S] [IsExtension A S]
    [Algebra B T] [IsExtension B T]
    [Algebra S T] [IsExtension S T]
    [Algebra S K₁] [IsFractionRing S K₁] [IsScalarTower A S K₁]
    [Algebra T E] [IsFractionRing T E] [IsScalarTower B T E]
    [Algebra S E] [IsScalarTower S K₁ E] [IsScalarTower S T E]
    (f : L ⊗[K] K₁ →ₐ[L] E) (hf : Function.Surjective f)
    (hfK₁ : ∀ a : K₁, f (Algebra.TensorProduct.includeRight a) = algebraMap K₁ E a)
    (hformal : RingHom.FormallySmoothNAdic.{max u v} (algebraMap A B)
      (IsLocalRing.maximalIdeal B)) :
    RingHom.FormallySmoothNAdic.{z} (algebraMap S T) (IsLocalRing.maximalIdeal T) := by
  let : Module.Finite L E := Module.Finite.of_surjective f.toLinearMap hf
  let : Algebra A E := ((algebraMap K₁ E).comp (algebraMap A K₁)).toAlgebra
  let : IsScalarTower A K₁ E := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A K E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K₁ E, IsScalarTower.algebraMap_apply A K K₁,
      ← IsScalarTower.algebraMap_apply K K₁ E]
  let : IsScalarTower A B E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K E, IsScalarTower.algebraMap_apply K L E,
      ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply B L E]
  obtain ⟨fS, hfS, p, hp, hpdef, eS, heS⟩ :=
    exists_integralClosure_localization_equiv A S K K₁
  obtain ⟨fT, hfT, q, hq, hqdef, eT, heT⟩ :=
    exists_integralClosure_localization_equiv B T L E
  let := hp
  let := hq
  obtain ⟨g, hg, hgA⟩ := exists_integralClosure_hom A B K₁ E
  have hdiag : fT.toRingHom.comp g = (algebraMap S T).comp fS.toRingHom := by
    ext a
    apply IsFractionRing.injective T E
    show algebraMap T E (fT (g a)) = algebraMap T E (algebraMap S T (fS a))
    rw [hfT, hg, ← IsScalarTower.algebraMap_apply S T E,
      IsScalarTower.algebraMap_apply S K₁ E, hfS]
  have hpq : q.comap g = p := by
    rw [hqdef, Ideal.comap_comap, hdiag, ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap, hpdef]
  have hginj : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply (algebraMap K₁ E).injective
    rw [← hg, ← hg, h]
  obtain ⟨ψ, hψinj, hψlocal, hψ⟩ := exists_injective_localRingHom g hginj p q hpq
  have hψformal : RingHom.FormallySmoothNAdic.{z} ψ
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) :=
    formallySmoothNAdic_tensorProduct_fieldFactor A B K L K₁ E
      f hf hfK₁ g hg p q hpq ψ hψ hformal
  have hcomm : eT.toRingHom.comp ψ = (algebraMap S T).comp eS.toRingHom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    show eT (ψ (algebraMap (integralClosure A K₁) _ a)) =
      algebraMap S T (eS (algebraMap (integralClosure A K₁) _ a))
    rw [hψ, heT, heS]
    exact RingHom.congr_fun hdiag a
  let : IsLocalHom eT.toRingHom := ⟨fun _ h ↦ by
    simpa using h.map eT.symm.toRingHom⟩
  have hmax : (IsLocalRing.maximalIdeal (Localization.AtPrime q)).map eT.toRingHom =
      IsLocalRing.maximalIdeal T := by
    rw [← IsLocalRing.maximalIdeal_comap eT.toRingHom]
    exact Ideal.map_comap_of_surjective eT.toRingHom eT.surjective _
  apply formallySmoothNAdic_of_equiv_square (algebraMap S T) ψ
    (IsLocalRing.maximalIdeal T) (IsLocalRing.maximalIdeal (Localization.AtPrime q))
    eS.symm eT.symm
  · ext s
    apply eT.injective
    show eT (eT.symm (algebraMap S T s)) = eT (ψ (eS.symm s))
    rw [eT.apply_symm_apply]
    have hc := RingHom.congr_fun hcomm (eS.symm s)
    change eT (ψ (eS.symm s)) = algebraMap S T (eS (eS.symm s)) at hc
    rw [eS.apply_symm_apply] at hc
    exact hc.symm
  · rw [← hmax, Ideal.map_map]
    simp
  · exact hψformal

theorem mem_of_surjective_tensorProduct
    {K L M E T : Type*} [CommRing K] [CommRing L] [CommRing M]
    [CommRing E] [CommRing T] [Algebra K L] [Algebra K M] [Algebra L E]
    (f : L ⊗[K] M →ₐ[L] E) (hf : Function.Surjective f)
    (g : E →+* T) (P : Subring T)
    (hL : ∀ l, g (algebraMap L E l) ∈ P)
    (hM : ∀ m, g (f (Algebra.TensorProduct.includeRight m)) ∈ P) :
    ∀ e, g e ∈ P := by
  intro e
  obtain ⟨t, rfl⟩ := hf e
  induction t using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using P.zero_mem
  | add x y hx hy => simpa only [map_add] using P.add_mem hx hy
  | tmul l m =>
    have heq : l ⊗ₜ[K] m = algebraMap L (L ⊗[K] M) l *
        Algebra.TensorProduct.includeRight m := by simp
    rw [heq, map_mul, map_mul]
    exact P.mul_mem (by simpa only [f.commutes] using hL l) (hM m)

@[ega "II 7.1.3" "partial"]
private theorem exists_integralClosure_hom_to_fractionRing
    (A S E F : Type*) [CommRing A] [CommRing S] [IsDomain S]
    [IsIntegrallyClosed S] [Field E] [Field F]
    [Algebra A S] [Algebra A E] [Algebra A F] [Algebra S F]
    [IsScalarTower A S F] [IsFractionRing S F] (f : E →ₐ[A] F) :
    ∃ g : integralClosure A E →ₐ[A] S,
      ∀ x, algebraMap S F (g x) = f (x : E) := by
  obtain ⟨g, hg⟩ := exists_integralClosure_hom_to_integrallyClosed A S F
  exact ⟨g.comp f.mapIntegralClosure, fun x ↦ hg (f.mapIntegralClosure x)⟩

set_option maxHeartbeats 1600000 in
-- Elaborating the many nested localization and tensor-product algebra structures here is
-- expensive.
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem formallySmoothNAdic_of_uniformizer_pow_eq
    (A : Type u) (B : Type v) (K L K₁ E S T : Type*)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Field L] [Field K₁] [Field E]
    [Algebra A B] [IsExtension A B]
    [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L]
    [Algebra K K₁] [Module.Finite K K₁] [Algebra A K₁] [IsScalarTower A K K₁]
    [Algebra K E] [Algebra L E] [Algebra K₁ E] [Algebra B E]
    [IsScalarTower K L E] [IsScalarTower K K₁ E] [IsScalarTower B L E]
    [Algebra A S] [IsExtension A S]
    [Algebra B T] [IsExtension B T]
    [Algebra S T] [IsExtension S T]
    [Algebra S K₁] [IsFractionRing S K₁] [IsScalarTower A S K₁]
    [Algebra T E] [IsFractionRing T E] [IsScalarTower B T E]
    [Algebra S E] [IsScalarTower S K₁ E] [IsScalarTower S T E]
    (f : L ⊗[K] K₁ →ₐ[L] E) (hf : Function.Surjective f)
    (hfK₁ : ∀ a : K₁, f (Algebra.TensorProduct.includeRight a) = algebraMap K₁ E a)
    (π : A) (hπ : Irreducible π) (θ : K₁)
    (hθ : θ ^ ramificationIndex A B = algebraMap A K₁ π)
    (he : 2 ≤ ramificationIndex A B)
    (htame : ringChar (IsLocalRing.ResidueField A) = 0 ∨
      Nat.Coprime (ringChar (IsLocalRing.ResidueField A))
          (ramificationIndex A B) ∧
        Algebra.IsSeparableExtension (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField B)) :
    RingHom.FormallySmoothNAdic.{z} (algebraMap S T) (IsLocalRing.maximalIdeal T) := by
  classical
  let n := ramificationIndex A B
  let P := Stacks.KummerExtension.kummerPoly K π n
  let : Fact (Irreducible P) := ⟨Stacks.KummerExtension.kummerPoly_irreducible K π n (by omega) hπ⟩
  let K₀ := Stacks.KummerExtension.K1 K π n
  let A₀ := Stacks.KummerExtension.A1 K π n
  let : IsDiscreteValuationRing A₀ := Stacks.KummerExtension.isDiscreteValuationRing_A1 K π n he hπ
  let : IsFractionRing A₀ K₀ := integralClosure.isFractionRing_of_finite_extension K K₀
  have hθP : P.eval₂ (algebraMap K K₁) θ = 0 := by
    simp only [P, Stacks.KummerExtension.kummerPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [hθ, ← IsScalarTower.algebraMap_apply A K K₁, sub_self]
  obtain ⟨hK₀K₁, hKK₀K₁, hK₀fin, hroot⟩ :=
    exists_finite_algebra_adjoinRoot_of_eval_eq_zero P θ hθP
  let := hK₀K₁
  let := hKK₀K₁
  let := hK₀fin
  let : Algebra A E := ((algebraMap K₁ E).comp (algebraMap A K₁)).toAlgebra
  let : IsScalarTower A K₁ E := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A K E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K₁ E, IsScalarTower.algebraMap_apply A K K₁,
      ← IsScalarTower.algebraMap_apply K K₁ E]
  let : IsScalarTower A B E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K E, IsScalarTower.algebraMap_apply K L E,
      ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply B L E]
  let : IsScalarTower A K₀ K₁ := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A K K₁, IsScalarTower.algebraMap_apply A K K₀,
      ← IsScalarTower.algebraMap_apply K K₀ K₁]
  let : Algebra K₀ E := ((algebraMap K₁ E).comp (algebraMap K₀ K₁)).toAlgebra
  let : IsScalarTower K₀ K₁ E := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower K K₀ E := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply K K₁ E, IsScalarTower.algebraMap_apply K K₀ K₁,
      ← IsScalarTower.algebraMap_apply K₀ K₁ E]
  have hxP : P.eval₂ (algebraMap K E) (algebraMap K₁ E θ) = 0 := by
    rw [IsScalarTower.algebraMap_eq K K₁ E, ← hom_eval₂, hθP, map_zero]
  have hxint : IsIntegral L (algebraMap K₁ E θ) := by
    have hmonic : (P.map (algebraMap K L)).Monic :=
      (monic_X_pow_sub_C (algebraMap A K π) (by omega : n ≠ 0)).map _
    refine ⟨P.map (algebraMap K L), hmonic, ?_⟩
    rw [eval₂_map, ← IsScalarTower.algebraMap_eq K L E]
    exact hxP
  obtain ⟨F, hF, hLF, hFE, hLFE, hFfin, f₀, hf₀, hrootF⟩ :=
    exists_tensorProduct_adjoinRoot_fieldFactor K L E P (algebraMap K₁ E θ) hxP hxint
  let := hF
  let := hLF
  let := hFE
  let := hLFE
  let := hFfin
  let : Algebra K F := ((algebraMap L F).comp (algebraMap K L)).toAlgebra
  let : IsScalarTower K L F := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower K F E := .of_algebraMap_eq fun k ↦ by
    rw [IsScalarTower.algebraMap_apply K L E, IsScalarTower.algebraMap_apply L F E]
    rfl
  let f₀right : K₀ →ₐ[K] F := (f₀.restrictScalars K).comp Algebra.TensorProduct.includeRight
  let : Algebra K₀ F := f₀right.toAlgebra
  let : IsScalarTower K K₀ F := .of_algebraMap_eq fun k ↦ (f₀right.commutes k).symm
  have hFroot : (algebraMap F E).comp (algebraMap K₀ F) = algebraMap K₀ E := by
    apply AdjoinRoot.ringHom_ext
    · ext k
      show algebraMap F E (algebraMap K₀ F (algebraMap K K₀ k)) =
        algebraMap K₀ E (algebraMap K K₀ k)
      rw [← IsScalarTower.algebraMap_apply K K₀ F,
        ← IsScalarTower.algebraMap_apply K F E, ← IsScalarTower.algebraMap_apply K K₀ E]
    · show algebraMap F E (f₀ (1 ⊗ₜ[K] AdjoinRoot.root P)) =
        algebraMap K₁ E (algebraMap K₀ K₁ (AdjoinRoot.root P))
      rw [hrootF, hroot]
  let : IsScalarTower K₀ F E := .of_algebraMap_eq fun k ↦ (RingHom.congr_fun hFroot k).symm
  let f₁ : F ⊗[K₀] K₁ →ₐ[F] E := Algebra.TensorProduct.lift
    (Algebra.ofId F E) (IsScalarTower.toAlgHom K₀ K₁ E) (fun _ _ ↦ Commute.all _ _)
  have hf₁K₁ (a : K₁) : f₁ (Algebra.TensorProduct.includeRight a) = algebraMap K₁ E a := by
    simp [f₁]
  have hf₁ : Function.Surjective f₁ := by
    intro e
    apply mem_of_surjective_tensorProduct f hf (RingHom.id E) f₁.range.toSubring
    · intro l
      exact ⟨algebraMap F (F ⊗[K₀] K₁) (algebraMap L F l), by
        show f₁ (algebraMap F _ (algebraMap L F l)) = algebraMap L E l
        rw [f₁.commutes, ← IsScalarTower.algebraMap_apply L F E]⟩
    · intro a
      exact ⟨Algebra.TensorProduct.includeRight a, (hf₁K₁ a).trans (hfK₁ a).symm⟩
  let : Algebra B F := ((algebraMap L F).comp (algebraMap B L)).toAlgebra
  let : IsScalarTower B L F := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower B F E := .of_algebraMap_eq fun b ↦ by
    rw [IsScalarTower.algebraMap_apply B L E, IsScalarTower.algebraMap_apply L F E]
    rfl
  obtain ⟨j, hj⟩ := exists_integralClosure_hom_to_fractionRing B T F E
    (IsScalarTower.toAlgHom B F E)
  change ∀ x, algebraMap T E (j x) = algebraMap F E (x : F) at hj
  let C₀ := integralClosure B F
  let q₀ : Ideal C₀ := (IsLocalRing.maximalIdeal T).comap j.toRingHom
  let : IsDedekindDomain C₀ :=
    (IsIntegralClosure.isDedekindDomain_and_comap_surjective_and_quasiFinite B L F C₀).1
  have hq₀0 : q₀ ≠ ⊥ := comap_maximalIdeal_ne_bot_of_algHom j
  let : q₀.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hq₀0
  let D₀ := Localization.AtPrime q₀
  let : IsDiscreteValuationRing D₀ :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain C₀ hq₀0 D₀
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply (algebraMap F E).injective
    rw [← hj, ← hj, h]
  obtain ⟨jloc, hjlocinj, hjloclocal, hjloc⟩ :=
    exists_injective_localizationAtPrime_lift j.toRingHom hjinj q₀ rfl
  let : Algebra D₀ T := jloc.toAlgebra
  let : IsLocalHom (algebraMap D₀ T) := hjloclocal
  let : FaithfulSMul D₀ T := (faithfulSMul_iff_algebraMap_injective D₀ T).mpr hjlocinj
  let : IsExtension D₀ T := ⟨⟩
  let : IsFractionRing C₀ F := integralClosure.isFractionRing_of_finite_extension L F
  obtain ⟨hD₀F, hC₀D₀F, hFracD₀⟩ := exists_fractionRing_localizationAtPrime_algebra C₀ F q₀
  let := hD₀F
  let := hC₀D₀F
  let := hFracD₀
  let : Algebra D₀ E := ((algebraMap F E).comp (algebraMap D₀ F)).toAlgebra
  let : IsScalarTower D₀ F E := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower D₀ T E := .of_algebraMap_eq fun d ↦ by
    have hd : (algebraMap T E).comp jloc = (algebraMap F E).comp (algebraMap D₀ F) := by
      apply IsLocalization.ringHom_ext q₀.primeCompl
      ext c
      show algebraMap T E (jloc (algebraMap C₀ D₀ c)) =
        algebraMap F E (algebraMap D₀ F (algebraMap C₀ D₀ c))
      rw [hjloc, ← IsScalarTower.algebraMap_apply C₀ D₀ F]
      exact hj c
    exact (RingHom.congr_fun hd d).symm
  let : IsScalarTower B D₀ F := .of_algebraMap_eq fun b ↦ by
    rw [IsScalarTower.algebraMap_apply B C₀ D₀, ← IsScalarTower.algebraMap_apply C₀ D₀ F]
    rfl
  let : IsLocalHom (algebraMap B D₀) := isLocalHom_localizationAtPrime_of_isIntegral B C₀ D₀ q₀
  let : FaithfulSMul B D₀ := (faithfulSMul_iff_algebraMap_injective B D₀).mpr (by
    intro a b h
    apply FaithfulSMul.algebraMap_injective B T
    have ha (b : B) : jloc (algebraMap B D₀ b) = algebraMap B T b := by
      rw [IsScalarTower.algebraMap_apply B C₀ D₀, hjloc]
      exact j.commutes b
    rw [← ha, ← ha, h])
  let : IsExtension B D₀ := ⟨⟩
  let : Algebra A F := ((algebraMap L F).comp (algebraMap A L)).toAlgebra
  let : IsScalarTower A L F := .of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A B F := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A L F, IsScalarTower.algebraMap_apply A B L,
      ← IsScalarTower.algebraMap_apply B L F]
  let : IsScalarTower A K₀ F := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A L F, IsScalarTower.algebraMap_apply A K L,
      ← IsScalarTower.algebraMap_apply K L F, IsScalarTower.algebraMap_apply K K₀ F,
      ← IsScalarTower.algebraMap_apply A K K₀]
  obtain ⟨g₀, hg₀, hg₀A⟩ := exists_integralClosure_hom A B K₀ F
  let : Algebra A₀ D₀ := ((algebraMap C₀ D₀).comp g₀).toAlgebra
  let : IsScalarTower A B D₀ := inferInstance
  let : IsScalarTower A A₀ D₀ := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A B D₀]
    show algebraMap B D₀ (algebraMap A B a) = algebraMap C₀ D₀ (g₀ (algebraMap A A₀ a))
    rw [hg₀A, ← IsScalarTower.algebraMap_apply B C₀ D₀]
  let : IsLocalHom (algebraMap A D₀) := by
    rw [IsScalarTower.algebraMap_eq A B D₀]
    infer_instance
  let : FaithfulSMul A D₀ := (faithfulSMul_iff_algebraMap_injective A D₀).mpr (by
    rw [IsScalarTower.algebraMap_eq A B D₀]
    exact (FaithfulSMul.algebraMap_injective B D₀).comp (FaithfulSMul.algebraMap_injective A B))
  let : IsExtension A D₀ := ⟨⟩
  let : IsScalarTower A₀ D₀ F := .of_algebraMap_eq fun a ↦ by
    show algebraMap K₀ F (a : K₀) = algebraMap D₀ F (algebraMap C₀ D₀ (g₀ a))
    rw [← IsScalarTower.algebraMap_apply C₀ D₀ F]
    exact (hg₀ a).symm
  let : IsLocalHom (algebraMap A₀ D₀) :=
    isLocalHom_algebraMap_of_isDiscreteValuationRing A A₀ D₀ π hπ.not_isUnit (by
      intro h
      have hK : algebraMap A K₀ π = 0 := congrArg Subtype.val h
      have hinj : Function.Injective (algebraMap A K₀) := by
        rw [IsScalarTower.algebraMap_eq A K K₀]
        exact (algebraMap K K₀).injective.comp (IsFractionRing.injective A K)
      exact hπ.ne_zero (hinj (hK.trans (map_zero _).symm)))
  let : FaithfulSMul A₀ D₀ := (faithfulSMul_iff_algebraMap_injective A₀ D₀).mpr (by
    intro a b h
    apply Subtype.ext
    apply (algebraMap K₀ F).injective
    show algebraMap A₀ F a = algebraMap A₀ F b
    rw [IsScalarTower.algebraMap_apply A₀ D₀ F, IsScalarTower.algebraMap_apply A₀ D₀ F]
    exact congrArg (algebraMap D₀ F) h)
  let : IsExtension A₀ D₀ := ⟨⟩
  let : IsLocalHom (algebraMap A A₀) := Stacks.LocalHom.isLocalHom_of_isIntegral A A₀
  let : FaithfulSMul A A₀ := (faithfulSMul_iff_algebraMap_injective A A₀).mpr (by
    intro a b h
    apply IsFractionRing.injective A K
    apply (algebraMap K K₀).injective
    exact congrArg Subtype.val h)
  let : IsExtension A A₀ := ⟨⟩
  have hbase : RingHom.FormallySmoothNAdic (algebraMap A₀ D₀)
      (IsLocalRing.maximalIdeal D₀) :=
    formallySmoothNAdic_over_root_uniformizer A B K L π n F D₀ q₀ hπ he rfl htame f₀ hf₀
  obtain ⟨i₀, hi₀⟩ := exists_integralClosure_hom_to_fractionRing A S K₀ K₁
    (IsScalarTower.toAlgHom A K₀ K₁)
  change ∀ x, algebraMap S K₁ (i₀ x) = algebraMap K₀ K₁ (x : K₀) at hi₀
  let : Algebra A₀ S := i₀.toAlgebra
  let : IsScalarTower A A₀ S := .of_algebraMap_eq fun a ↦ (i₀.commutes a).symm
  let : IsScalarTower A₀ K₀ K₁ := inferInstance
  let : IsScalarTower A₀ S K₁ := .of_algebraMap_eq fun a ↦ (hi₀ a).symm
  let : IsLocalHom (algebraMap A₀ S) :=
    isLocalHom_algebraMap_of_isDiscreteValuationRing A A₀ S π hπ.not_isUnit (by
      intro h
      exact hπ.ne_zero ((FaithfulSMul.algebraMap_injective A A₀) (h.trans (map_zero _).symm)))
  let : FaithfulSMul A₀ S := (faithfulSMul_iff_algebraMap_injective A₀ S).mpr (by
    intro a b h
    apply Subtype.ext
    apply (algebraMap K₀ K₁).injective
    rw [← hi₀, ← hi₀]
    exact congrArg (algebraMap S K₁) h)
  let : IsExtension A₀ S := ⟨⟩
  let : IsScalarTower A₀ K₀ F := inferInstance
  exact formallySmoothNAdic_of_fractionRing_baseChange A₀ D₀ K₀ F K₁ E S T
    f₁ hf₁ hf₁K₁ hbase

end

end IsDiscreteValuationRing
