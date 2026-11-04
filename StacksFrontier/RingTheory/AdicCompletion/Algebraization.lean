module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.AdicCompletion.QuotEquivMapPow
public import StacksFrontier.RingTheory.AdicCompletion.SectionsAlgebra
public import StacksFrontier.RingTheory.Idempotents.Lifting
public import StacksFrontier.RingTheory.Localization.Idempotent
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingModuleProperties
public import StacksFrontier.RingTheory.AdicCompletion.SmulTopPow
public import StacksFrontier.RingTheory.Etale.LiftIdempotentsAndModules
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.AdicCompletion.OfTensorProductBijective

/-!
# Algebraizing a quotient of an adic completion

Let `A` be a Noetherian ring, `I` an ideal of `A`, and `B` a finite-type `A`-algebra. If a
quotient `C` of the `I`-adic completion of `B` has conormal module annihilated by a power of `I`,
then `C` is the completion of a finite-type `A`-algebra.

## Main results

* `exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated` algebraizes a
  quotient of an adic completion whose conormal module is annihilated by a power of the ideal.
* `ofTensorProductAlgEquiv` identifies the `ID`-adic completion of a finite `R`-algebra `D` with
  the base change of `D` to the `I`-adic completion of `R`.

## Implementation notes

The `I`-adic completion of an `A`-algebra `B` is represented by
`AdicCompletion (I.map (algebraMap A B)) B`. The conormal module `J / J ^ 2` is Mathlib's
`Ideal.Cotangent J`, and annihilation by `I ^ c` is expressed through its natural `A`-module
structure. The isomorphism in the conclusion is an `A`-algebra equivalence, retaining its
compatibility with the canonical maps from `A`.

No universe specialization is imposed: the three carriers `A`, `B`, `C` live in independent
universes `u`, `v`, `w`, and the algebraization `D` is produced in `Type (max u v w)`, which is
the universe in which the gluing construction naturally lands.

## References

* [Stacks Project, Tag 0ALR](https://stacks.math.columbia.edu/tag/0ALR)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

private theorem mul_mem_pow_two_of_cotangent_annihilated
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
    (J : Ideal R) (I : Ideal A) (c : ℕ)
    (hJ : I ^ c • (⊤ : Submodule A J.Cotangent) = ⊥)
    {a : A} (ha : a ∈ I ^ c) {x : R} (hx : x ∈ J) :
    algebraMap A R a * x ∈ J ^ 2 := by
  have hz : a • J.toCotangent ⟨x, hx⟩ = 0 := by
    have hm := Submodule.smul_mem_smul ha
      (Submodule.mem_top : J.toCotangent ⟨x, hx⟩ ∈ (⊤ : Submodule A J.Cotangent))
    rw [hJ] at hm
    exact hm
  have hz' : J.toCotangent ((algebraMap A R a) • (⟨x, hx⟩ : J)) = 0 := by
    rw [map_smul, IsScalarTower.algebraMap_smul]
    exact hz
  exact (J.toCotangent_eq_zero _).mp hz'

private theorem isIdempotentElem_map_of_mul_mem_pow_two
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (g : R →+* S) (J : Ideal R) {a : R} (ha : IsUnit (g a))
    (hJ : ∀ x ∈ J, a * x ∈ J ^ 2) : IsIdempotentElem (J.map g) := by
  apply le_antisymm Ideal.mul_le_left
  rw [← Ideal.map_mul, Ideal.map_le_iff_le_comap]
  intro x hx
  have hm : g a * g x ∈ (J * J).map g := by
    simpa [pow_two] using Ideal.mem_map_of_mem g (hJ x hx)
  exact (Ideal.unit_mul_mem_iff_mem _ ha).mp hm

private theorem ker_away_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (g : R →+* S) (a : R) :
    RingHom.ker (IsLocalization.Away.map (Localization.Away a)
      (Localization.Away (g a)) g a) =
        (RingHom.ker g).map (algebraMap R (Localization.Away a)) :=
  IsLocalization.ker_map (Localization.Away (g a)) g (Submonoid.map_powers g a)

private theorem isLocalizationAtIdempotent_of_surjective_of_isIdempotentElem_ker
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : Function.Surjective g)
    (hfg : (RingHom.ker g).FG) (hi : IsIdempotentElem (RingHom.ker g)) :
    IsLocalizationAtIdempotent g := by
  obtain ⟨e, he, hker⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).mp hi
  let := g.toAlgebra
  refine ⟨1 - e, he.one_sub, ?_⟩
  apply IsLocalization.away_of_isIdempotentElem he.one_sub
  · show RingHom.ker g = Ideal.span {1 - (1 - e)}
    simpa [Ideal.submodule_span_eq] using hker
  · exact hg

private theorem map_smul_cotangent_eq_bot
    {A : Type u} {R : Type v} [CommRing A] [CommRing R] [Algebra A R]
    (J : Ideal R) (I : Ideal A)
    (hJ : I • (⊤ : Submodule A J.Cotangent) = ⊥) :
    I.map (algebraMap A R) • (⊤ : Submodule R J.Cotangent) = ⊥ := by
  apply (Submodule.restrictScalars_injective A)
  simpa only [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top,
    Submodule.restrictScalars_bot] using hJ

private theorem isLocalizationAtIdempotent_away_map_of_cotangent_annihilated
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (g : R →+* S) (hg : Function.Surjective g)
    (hfg : (RingHom.ker g).FG) (I : Ideal R) (c : ℕ)
    (hJ : I ^ c • (⊤ : Submodule R (RingHom.ker g).Cotangent) = ⊥)
    {a : R} (ha : a ∈ I) :
    IsLocalizationAtIdempotent
      (IsLocalization.Away.map (Localization.Away a) (Localization.Away (g a)) g a) := by
  let g' := IsLocalization.Away.map (Localization.Away a) (Localization.Away (g a)) g a
  apply isLocalizationAtIdempotent_of_surjective_of_isIdempotentElem_ker g'
  · apply (IsLocalization.Away.map_surjective_iff _ _ g a).mpr
    intro x
    obtain ⟨y, rfl⟩ := hg x
    exact ⟨y, 0, by simp⟩
  · rw [ker_away_map]
    exact hfg.map _
  · rw [ker_away_map]
    apply isIdempotentElem_map_of_mul_mem_pow_two _ _ (a := a ^ c)
      (by simpa only [map_pow] using
        (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away a) a).pow c)
    intro x hx
    exact mul_mem_pow_two_of_cotangent_annihilated _ I c hJ (Ideal.pow_mem_pow ha c) hx

private theorem exists_surjective_prod_awayMap_bijective_of_cotangent_annihilated
    {A : Type u} {R : Type v} {C : Type w} [CommRing A] [CommRing R]
    [CommRing C] [Algebra A R] [Algebra R C] [IsNoetherianRing R]
    (I : Ideal A) (hI : I.FG) (c : ℕ)
    (hC : Function.Surjective (algebraMap R C))
    (hJ : I ^ c • (⊤ : Submodule A (RingHom.ker (algebraMap R C)).Cotangent) = ⊥) :
    ∃ (C' : Type v) (_ : CommRing C') (_ : Algebra R C'),
      Function.Surjective (algebraMap R C') ∧ Module.Finite R (C × C') ∧
      ∀ f ∈ I.map (algebraMap A R), Function.Bijective
        (IsLocalization.Away.map (Localization.Away f)
          (Localization.Away (algebraMap R (C × C') f)) (algebraMap R (C × C')) f) := by
  have hJR : (I.map (algebraMap A R)) ^ c •
      (⊤ : Submodule R (RingHom.ker (algebraMap R C)).Cotangent) = ⊥ := by
    rw [← Ideal.map_pow]
    exact map_smul_cotangent_eq_bot _ _ hJ
  obtain ⟨C', _, _, hC', hloc⟩ :=
    exists_surjective_bijective_away_prod
    (I.map (algebraMap A R)) (hI.map _) (fun _ hf =>
      isLocalizationAtIdempotent_away_map_of_cotangent_annihilated _ hC
        (Ideal.fg_of_isNoetherianRing _) _ c hJR hf)
  have : Module.Finite R C := Module.Finite.of_surjective (Algebra.linearMap R C) hC
  have : Module.Finite R C' := Module.Finite.of_surjective (Algebra.linearMap R C') hC'
  exact ⟨C', inferInstance, inferInstance, hC', inferInstance, hloc⟩

open TensorProduct

/-- For a finite `R`-algebra `D` over a Noetherian ring `R`, the canonical `R`-linear comparison
map from `AdicCompletion I R ⊗[R] D` to the `ID`-adic completion of `D`. -/
noncomputable def ofTensorProductLinearEquiv
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (D : Type*) [CommRing D] [Algebra R D] [Module.Finite R D] :
    TensorProduct R (AdicCompletion I R) D ≃ₗ[R]
      AdicCompletion (I.map (algebraMap R D)) D :=
  ((LinearEquiv.ofBijective (AdicCompletion.ofTensorProduct I D)
    (AdicCompletion.bijective_ofTensorProduct I D)).restrictScalars R).trans
      (adicCompletionLinearEquivMap I D)

/-- The value of `ofTensorProductLinearEquiv` on a pure tensor, read in the `n`-th stage of the
tower. -/
theorem ofTensorProductLinearEquiv_tmul_eval
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (D : Type*) [CommRing D] [Algebra R D] [Module.Finite R D]
    (a : AdicCompletion I R) (d : D) (n : ℕ) :
    AdicCompletion.evalₐ (I.map (algebraMap R D)) n
        (ofTensorProductLinearEquiv I D (a ⊗ₜ[R] d)) =
      Ideal.quotientMap ((I.map (algebraMap R D)) ^ n) (algebraMap R D)
          (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)
          (AdicCompletion.evalₐ I n a) *
        Ideal.Quotient.mk ((I.map (algebraMap R D)) ^ n) d := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I R a
  show AdicCompletion.evalₐ _ n (adicCompletionLinearEquivMap I D
    (AdicCompletion.ofTensorProduct I D (AdicCompletion.mk I R a ⊗ₜ[R] d))) = _
  rw [AdicCompletion.ofTensorProduct_tmul, AdicCompletion.evalₐ_mk]
  rw [← AdicCompletion.factor_eval_eq_evalₐ _ _ (by simp)]
  show Ideal.Quotient.factorₐ D (by simp)
    (quotEquivMapPow I D n ((AdicCompletion.mk I R a • AdicCompletion.of I D d).val n)) = _
  simp only [AdicCompletion.smul_eval, AdicCompletion.mk_apply_coe,
    AdicCompletion.of_apply, Submodule.mkQ_apply]
  show Ideal.Quotient.factorₐ D (by simp)
    (quotEquivMapPow I D n (Submodule.Quotient.mk (a n • d))) = _
  rw [quotEquivMapPow_mk]
  simp only [Ideal.quotientMap_mk, map_mul, Algebra.smul_def]
  rfl

/-- For a finite `R`-algebra `D` over a Noetherian ring `R`, the `ID`-adic completion of `D` is the
base change of `D` to the `I`-adic completion of `R`, as `R`-algebras. -/
@[sga "1 III 1.6" "more general"]
noncomputable def ofTensorProductAlgEquiv
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (D : Type*) [CommRing D] [Algebra R D] [Module.Finite R D] :
    TensorProduct R (AdicCompletion I R) D ≃ₐ[R]
      AdicCompletion (I.map (algebraMap R D)) D :=
  Algebra.TensorProduct.algEquivOfLinearEquivTensorProduct
    (ofTensorProductLinearEquiv I D)
    (by
      intro a₁ a₂ d₁ d₂
      apply AdicCompletion.ext_evalₐ
      intro n
      simp only [map_mul, ofTensorProductLinearEquiv_tmul_eval]
      ring)
    (by
      apply AdicCompletion.ext_evalₐ
      intro n
      rw [ofTensorProductLinearEquiv_tmul_eval]
      simp)

private theorem baseChange_bijective_of_idealPowerTorsion
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) [Module.Flat R S]
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M]
    (hM : IsIPowerTorsion R M I) :
    Function.Bijective ((TensorProduct.mk R M S).flip 1) := by
  let e : ULift.{max u v} M ≃ₗ[R] M := ULift.moduleEquiv
  have hM' : IsIPowerTorsion R (ULift.{max u v} M) I := by
    intro m
    obtain ⟨n, hn, hnm⟩ := hM (e m)
    refine ⟨n, hn, fun a ha => e.injective ?_⟩
    simpa only [map_smul, map_zero] using hnm a ha
  have h :=
    (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective
      R S I inferInstance).mpr hq (ULift.{max u v} M) hM'
  let E := TensorProduct.congr e (LinearEquiv.refl R S)
  have hcomp : Function.Bijective
      (((TensorProduct.mk R M S).flip 1) ∘ e) := by
    have heq : ((TensorProduct.mk R M S).flip 1) ∘ e =
        E ∘ ((TensorProduct.mk R (ULift.{max u v} M) S).flip 1) := by
      funext m
      simp [E]
    rw [heq]
    exact E.bijective.comp h
  exact (Function.Bijective.of_comp_iff _ e.bijective).mp hcomp

/-- Compatible algebra equivalences on all infinitesimal neighbourhoods induce an algebra
equivalence on their adic completions. -/
public noncomputable def adicCompletionAlgEquivOfQuotientEquiv
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] (I : Ideal R) (J : Ideal S)
    (e : ∀ n : ℕ, (R ⧸ I ^ n) ≃ₐ[A] (S ⧸ J ^ n))
    (he : ∀ {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n),
      Ideal.Quotient.factorPow J h (e n x) =
        e m (Ideal.Quotient.factorPow I h x)) :
    AdicCompletion I R ≃ₐ[A] AdicCompletion J S := by
  let F := AdicCompletion.liftAlgHom J
    (fun n => (e n).toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars A))
    (fun {m n} h => by
      ext x
      exact (he h _).trans (congrArg (e m) (AdicCompletion.factorPow_evalₐ I h x)))
  let G := AdicCompletion.liftAlgHom I
    (fun n => (e n).symm.toAlgHom.comp ((AdicCompletion.evalₐ J n).restrictScalars A))
    (fun {m n} h => by
      ext x
      apply (e m).injective
      change e m (Ideal.Quotient.factorPow I h
        ((e n).symm (AdicCompletion.evalₐ J n x))) =
          e m ((e m).symm (AdicCompletion.evalₐ J m x))
      rw [← he, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
      exact AdicCompletion.factorPow_evalₐ J h x)
  exact
    { F with
      invFun := G
      left_inv := fun x => AdicCompletion.ext_evalₐ fun n => by simp [F, G]
      right_inv := fun x => AdicCompletion.ext_evalₐ fun n => by simp [F, G] }

/-- A flat algebra map that is an isomorphism modulo an ideal induces an isomorphism on
adic completions, compatible with the original algebra map. -/
public theorem exists_adicCompletionAlgEquiv_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) [Module.Flat R S]
    (hq : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map)) :
    ∃ E : AdicCompletion I R ≃ₐ[R] AdicCompletion (I.map (algebraMap R S)) S,
      ∀ r : R, E (algebraMap R (AdicCompletion I R) r) =
        algebraMap S (AdicCompletion (I.map (algebraMap R S)) S) (algebraMap R S r) := by
  let q (n : ℕ) : (R ⧸ I ^ n) →ₐ[R] (S ⧸ (I ^ n).map (algebraMap R S)) :=
    { __ := Ideal.quotientMap _ (algebraMap R S) Ideal.le_comap_map
      commutes' _ := rfl }
  let e n := (AlgEquiv.ofBijective (q n) (quotientMap_pow_bijective_of_flat I hq n)).trans
    (Ideal.quotientEquivAlgOfEq R (Ideal.map_pow (algebraMap R S) I n))
  have he {m n : ℕ} (h : m ≤ n) (x : R ⧸ I ^ n) :
      Ideal.Quotient.factorPow (I.map (algebraMap R S)) h (e n x) =
        e m (Ideal.Quotient.factorPow I h x) := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  refine ⟨adicCompletionAlgEquivOfQuotientEquiv I _ e he, fun r => ?_⟩
  exact (adicCompletionAlgEquivOfQuotientEquiv I _ e he).commutes r

/-- Completion commutes with quotients over a Noetherian ring. -/
public noncomputable def adicCompletionQuotientAlgEquiv
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I J : Ideal R) :
    (AdicCompletion I R ⧸ J.map (algebraMap R (AdicCompletion I R))) ≃ₐ[R]
      AdicCompletion (I.map (algebraMap R (R ⧸ J))) (R ⧸ J) :=
  ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (AdicCompletion I R) J).restrictScalars
    R).trans (ofTensorProductAlgEquiv I (R ⧸ J))

/-- Extending an ideal of `A` along `A → R → S` is the same as extending it directly to `S`. -/
private theorem map_map_algebraMap_of_isScalarTower
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra R S]
    [Algebra A S] [IsScalarTower A R S] (I : Ideal A) :
    (I.map (algebraMap A R)).map (algebraMap R S) = I.map (algebraMap A S) := by
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

private theorem exists_etale_idempotent_lift
    {R : Type u} [CommRing R] (I : Ideal R)
    (e : R ⧸ I) (he : IsIdempotentElem e) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Algebra.Etale R S ∧
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
          Ideal.le_comap_map) ∧
      ∃ s : S, IsIdempotentElem s ∧
        Ideal.Quotient.mk (I.map (algebraMap R S)) s =
          Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S)
            Ideal.le_comap_map e := by
  have hI : I.map (algebraMap R R) = I := by simp
  let e₀ := (Ideal.quotientEquivAlgOfEq R hI).symm e
  have he₀ : IsIdempotentElem e₀ := he.map (Ideal.quotientEquivAlgOfEq R hI).symm
  obtain ⟨S, _, _, s, het, hquot, hs, hlift⟩ :=
    exists_etale_baseChange_idempotent_lift I e₀ he₀
  let L : TensorProduct R R S ≃ₐ[R] S := Algebra.TensorProduct.lid R S
  refine ⟨S, inferInstance, inferInstance, het, hquot, L s, hs.map L, ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective e
  let ι : R →+* TensorProduct R R S := Algebra.TensorProduct.includeLeftRingHom
  have hd : s - ι r ∈ (I.map (algebraMap R R)).map ι := Ideal.Quotient.eq.mp hlift.symm
  have hm : ((I.map (algebraMap R R)).map ι).map L.toRingHom =
      I.map (algebraMap R S) := by
    rw [hI, Ideal.map_map]
    congr 1
    ext a
    simp [L, ι, Algebra.smul_def]
  have hd' := Ideal.mem_map_of_mem L.toRingHom hd
  rw [hm] at hd'
  apply Ideal.Quotient.eq.mpr
  simpa [L, ι, Algebra.smul_def] using hd'

/-- A factor of an adic completion defined by an idempotent is the completion of a
finite-type algebra. -/
private theorem exists_finiteType_adicCompletion_quotient_idempotent
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (e : AdicCompletion I R) (he : IsIdempotentElem e) :
    ∃ (D : Type u) (_ : CommRing D) (_ : Algebra R D),
      Algebra.FiniteType R D ∧
        Nonempty ((AdicCompletion I R ⧸ Ideal.span {1 - e}) ≃ₐ[R]
          AdicCompletion (I.map (algebraMap R D)) D) := by
  obtain ⟨S, _, _, het, hq, s, hs, hse⟩ :=
    exists_etale_idempotent_lift I (AdicCompletion.evalOneₐ I e)
      (he.map (AdicCompletion.evalOneₐ I))
  have := het
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  obtain ⟨E, hE⟩ := exists_adicCompletionAlgEquiv_of_flat (S := S) I hq
  let J := I.map (algebraMap R S)
  let K := J.map (algebraMap S (AdicCompletion J S))
  have : IsAdicComplete K (AdicCompletion J S) :=
    AdicCompletion.isAdicComplete_self J (Ideal.fg_of_isNoetherianRing _)
  have hmap : (I.map (algebraMap R (AdicCompletion I R))).map E.toRingHom = K := by
    rw [Ideal.map_map]
    show I.map _ = (I.map (algebraMap R S)).map (algebraMap S (AdicCompletion J S))
    rw [Ideal.map_map]
    congr 1
    ext r : 1
    exact hE r
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I e)
  have her : e - algebraMap R (AdicCompletion I R) r ∈
      I.map (algebraMap R (AdicCompletion I R)) := by
    rw [← AdicCompletion.ker_evalOneₐ_eq_map I (Ideal.fg_of_isNoetherianRing _)]
    apply RingHom.mem_ker.mpr
    simp only [map_sub]
    exact sub_eq_zero.mpr hr.symm
  have hsR : s - algebraMap R S r ∈ J := by
    apply Ideal.Quotient.eq.mp
    rw [hse, ← hr]
    rfl
  have hsE : algebraMap S (AdicCompletion J S) s = E e := by
    apply IsIdempotentElem.eq_of_sub_mem_jacobson (hs.map (algebraMap S _)) (he.map E)
    apply HenselianRing.jac (I := K)
    have h₁ := Ideal.mem_map_of_mem (algebraMap S (AdicCompletion J S)) hsR
    have h₂ := Ideal.mem_map_of_mem E.toRingHom her
    rw [hmap] at h₂
    simp only [map_sub] at h₁ h₂
    have h := K.sub_mem h₁ h₂
    change algebraMap S (AdicCompletion J S) s -
        algebraMap S (AdicCompletion J S) (algebraMap R S r) -
        (E e - E (algebraMap R (AdicCompletion I R) r)) ∈ K at h
    rw [hE] at h
    convert h using 1
    ring
  let L : Ideal S := Ideal.span {1 - s}
  have hL : L.map (algebraMap S (AdicCompletion J S)) =
      (Ideal.span {1 - e}).map E.toRingHom := by
    simp only [L, Ideal.map_span, Set.image_singleton, map_sub, map_one, hsE]
    rfl
  let Q := S ⧸ L
  have hIQ : J.map (algebraMap S Q) = I.map (algebraMap R Q) :=
    map_map_algebraMap_of_isScalarTower I
  let F := (Ideal.quotientEquivAlg _ _ E hL).trans
    ((adicCompletionQuotientAlgEquiv J L).restrictScalars R)
  refine ⟨Q, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  show (AdicCompletion I R ⧸ Ideal.span {1 - e}) ≃ₐ[R] AdicCompletion _ Q
  rw [← hIQ]
  exact F

private theorem ker_fst_comp_algEquiv_prod
    {A R C C' : Type*} [CommRing A] [CommRing R] [CommRing C] [CommRing C']
    [Algebra A R] [Algebra A C] [Algebra A C'] (E : R ≃ₐ[A] C × C') :
    RingHom.ker ((AlgHom.fst A C C').comp E.toAlgHom).toRingHom =
      Ideal.span {1 - E.symm (1, 0)} := by
  apply le_antisymm
  · intro x hx
    have hx' : (E x).1 = 0 := hx
    rw [Ideal.mem_span_singleton]
    refine ⟨x, E.injective ?_⟩
    simp only [map_mul, map_sub, map_one, AlgEquiv.apply_symm_apply]
    ext <;> simp [hx']
  · refine Ideal.span_le.mpr ?_
    rintro _ rfl
    show (E (1 - E.symm (1, 0))).1 = 0
    simp

/-- If a product algebra is a completion, each factor is a completion of a finite-type
algebra over the same base. -/
private theorem exists_finiteType_adicCompletion_of_prod
    {A : Type u} {R : Type v} {C : Type w} {C' : Type*}
    [CommRing A] [CommRing R] [IsNoetherianRing R] [CommRing C] [CommRing C']
    [Algebra A R] [Algebra.FiniteType A R] [Algebra A C] [Algebra A C']
    (I : Ideal A) (E : AdicCompletion (I.map (algebraMap A R)) R ≃ₐ[A] C × C') :
    ∃ (D : Type v) (_ : CommRing D) (_ : Algebra A D),
      Algebra.FiniteType A D ∧
        Nonempty (C ≃ₐ[A] AdicCompletion (I.map (algebraMap A D)) D) := by
  let J := I.map (algebraMap A R)
  let e := E.symm (1, 0)
  have he : IsIdempotentElem e :=
    (show IsIdempotentElem ((1, 0) : C × C') from by ext <;> simp).map E.symm
  obtain ⟨D, _, _, hD, ⟨F⟩⟩ :=
    exists_finiteType_adicCompletion_quotient_idempotent J e he
  let : Algebra A D := Algebra.compHom D (algebraMap A R)
  have : IsScalarTower A R D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := hD
  have : Algebra.FiniteType A D :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType A R) hD
  let p : AdicCompletion J R →ₐ[A] C := (AlgHom.fst A C C').comp E.toAlgHom
  have hp : Function.Surjective p := fun c =>
    ⟨E.symm (c, 0), congrArg Prod.fst (E.apply_symm_apply (c, 0))⟩
  let G := (Ideal.quotientKerAlgEquivOfSurjective hp).symm.trans
    (Ideal.quotientEquivAlgOfEq A (ker_fst_comp_algEquiv_prod E))
  have hID : J.map (algebraMap R D) = I.map (algebraMap A D) :=
    map_map_algebraMap_of_isScalarTower I
  refine ⟨D, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  rw [← hID]
  exact G.trans (F.restrictScalars A)

/-- An algebra isomorphism `R ≃ₐ[A] S` induces one of the adic completions along the
extensions of an ideal of `A`. -/
noncomputable def adicCompletionCongr
    {A R S : Type*} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S] (I : Ideal A) (E : R ≃ₐ[A] S) :
    AdicCompletion (I.map (algebraMap A R)) R ≃ₐ[A]
      AdicCompletion (I.map (algebraMap A S)) S := by
  have hmap : (I.map (algebraMap A R)).map (E : R →+* S) = I.map (algebraMap A S) := by
    rw [Ideal.map_map]
    congr 1
    exact E.toAlgHom.comp_algebraMap
  let e n := Ideal.quotientEquivAlg ((I.map (algebraMap A R)) ^ n)
    ((I.map (algebraMap A S)) ^ n) E (by rw [Ideal.map_pow, hmap])
  refine adicCompletionAlgEquivOfQuotientEquiv _ _ e ?_
  intro m n h x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

open CategoryTheory FormalGlueing

attribute [local instance] restrictScalarsCommRing

attribute [local instance] restrictScalarsCommRing restrictScalarsAlgebra
attribute [local instance] LocalizedModule.algebraOfIsLocalization

attribute [local instance] canonicalLocalCommRing

attribute [local instance] canonicalLocalAlgebra

private theorem localizedModuleMap_bijective_of_linearEquiv
    {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (S : Submonoid R) (e : M ≃ₗ[R] N) :
    Function.Bijective (LocalizedModule.map S e.toLinearMap) := by
  have h (g : N →ₗ[R] M) (hg : g.comp e.toLinearMap = LinearMap.id) (x) :
      LocalizedModule.map S g (LocalizedModule.map S e.toLinearMap x) = x := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk]
      exact congrArg (LocalizedModule.mk · s) (LinearMap.congr_fun hg m)
  have h' (x) : LocalizedModule.map S e.toLinearMap
      (LocalizedModule.map S e.symm.toLinearMap x) = x := by
    induction x using LocalizedModule.induction_on with
    | h m s => simp [LocalizedModule.map_mk]
  exact ⟨Function.LeftInverse.injective (h e.symm.toLinearMap (by ext; simp)),
    Function.RightInverse.surjective h'⟩

/-- **Stacks Tag 0ALR.** A quotient of the adic completion of a finite-type algebra is itself
the adic completion of a finite-type algebra if its conormal module is annihilated by a power of
the defining ideal. -/
@[stacks 0ALR]
theorem exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated
    (A : Type u) (B : Type v) (C : Type w) [CommRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    [CommRing C] [Algebra A C] (I : Ideal A)
    (φ : AdicCompletion (I.map (algebraMap A B)) B →ₐ[A] C)
    (hφ : Function.Surjective φ) (c : ℕ)
    (hJ : I ^ c • (⊤ : Submodule A (RingHom.ker φ.toRingHom).Cotangent) = ⊥) :
    ∃ (D : Type (max u v w)) (_ : CommRing D) (_ : Algebra A D),
      Algebra.FiniteType A D ∧
        Nonempty (C ≃ₐ[A] AdicCompletion (I.map (algebraMap A D)) D) := by
  let R := AdicCompletion (I.map (algebraMap A B)) B
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let : Algebra R C := φ.toRingHom.toAlgebra
  obtain ⟨C', _, _, hC', hfinite, hloc⟩ :=
    exists_surjective_prod_awayMap_bijective_of_cotangent_annihilated
      (R := R) (C := C) I I.fg_of_isNoetherianRing c hφ hJ
  have : Module.Finite R (C × C') := hfinite
  have : IsScalarTower A R C := IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  let : Algebra A C' := Algebra.compHom C' (algebraMap A R)
  have : IsScalarTower A R C' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let T := C × C'
  let : Algebra B T := Algebra.compHom T (algebraMap B R)
  have : IsScalarTower B R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B T := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    show algebraMap A T a = algebraMap R T (algebraMap B R (algebraMap A B a))
    rw [← IsScalarTower.algebraMap_apply A B R, ← IsScalarTower.algebraMap_apply A R T]
  obtain ⟨r, f, hf⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      (Ideal.fg_of_isNoetherianRing (I.map (algebraMap A B)))
  have hflat : Module.Flat B R := AdicCompletion.flat_of_isNoetherian _
  have hquot : Function.Bijective
      (Ideal.quotientMap ((Ideal.span (Set.range f)).map (algebraMap B R))
        (algebraMap B R) Ideal.le_comap_map) := by
    have hf' : Ideal.span (Set.range f) = I.map (algebraMap A B) := hf
    rw [hf']
    exact AdicCompletion.quotientMap_bijective _ (Ideal.fg_of_isNoetherianRing _)
  let B' := ULift.{w} B
  let eB : R ⊗[B] B' ≃ₐ[R] R :=
    (Algebra.TensorProduct.congr AlgEquiv.refl ULift.algEquiv).trans
      (Algebra.TensorProduct.rid B R R)
  let q : R ⊗[B] B' →ₐ[R] T := (Algebra.ofId R T).comp eB.toAlgHom
  have hq : ∀ i, Function.Bijective
      (LocalizedModule.map (Submonoid.powers (algebraMap B R (f i))) q.toLinearMap) := by
    intro i
    have hmem : algebraMap B R (f i) ∈ I.map (algebraMap A R) := by
      rw [IsScalarTower.algebraMap_eq A B R, ← Ideal.map_map]
      apply Ideal.mem_map_of_mem
      rw [← hf]
      exact Submodule.subset_span ⟨i, rfl⟩
    have h1 := localizedModuleMap_bijective_of_awayMap_bijective _ (hloc _ hmem)
    have h2 := localizedModuleMap_bijective_of_linearEquiv
      (Submonoid.powers (algebraMap B R (f i))) eB.toLinearEquiv
    have h3 := localizedModuleMap_bijective_comp _ _ _ h2 h1
    exact h3
  let D := sectionsSubalgebra.{v, v, w} f B' T q hq
  have : Module.Finite B B' := Module.Finite.equiv ULift.moduleEquiv.symm
  have : Module.Finite B D := finite_sectionsSubalgebra f B' T q hq hflat hquot
  obtain ⟨E, -⟩ := exists_algEquiv_tensor_sectionsSubalgebra f B' T q hq hflat hquot
  let : Algebra A D := Algebra.compHom D (algebraMap A B)
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType B D := inferInstance
  have : Algebra.FiniteType A D := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType A B)
    this
  have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A D
  have hID : (I.map (algebraMap A B)).map (algebraMap B D) = I.map (algebraMap A D) :=
    map_map_algebraMap_of_isScalarTower I
  let F : AdicCompletion (I.map (algebraMap A D)) D ≃ₐ[A] C × C' := by
    rw [← hID]
    exact ((ofTensorProductAlgEquiv (I.map (algebraMap A B)) D).symm.restrictScalars A).trans
      ((E.restrictScalars B).restrictScalars A)
  obtain ⟨D₀, _, _, hD₀, ⟨G⟩⟩ := exists_finiteType_adicCompletion_of_prod I F
  let D₁ := ULift.{max u v w} D₀
  have : Algebra.FiniteType A D₁ := Algebra.FiniteType.equiv hD₀ ULift.algEquiv.symm
  exact ⟨D₁, inferInstance, inferInstance, this,
    ⟨G.trans (adicCompletionCongr I ULift.algEquiv.symm)⟩⟩

end
