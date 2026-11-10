module

public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic.RankStrata

/-!
# The determinant line is invertible

The determinant line of a finite projective module is finite projective, of rank one at every
prime.

## Main results

* `ProjectiveDeterminant.invertible`: the determinant line is finite projective of rank one.
* `ProjectiveDeterminant.rankAtStalk_eq_one`: at every prime the determinant line has rank one.
-/

namespace ProjectiveDeterminant

section

universe u v w

@[expose] public section

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

section Invertibility

open TensorProduct

variable {P : Type*} [AddCommGroup P] [Module R P]

/-- Submodules on which pairwise orthogonal idempotents act as the identity are independent. -/
private theorem iSupIndep_of_orthogonal_idempotents
    {ι : Type*} {N : Type*} [AddCommGroup N] [Module R N]
    (e : ι → R) (P : ι → Submodule R N)
    (he : Pairwise fun i j => e i * e j = 0)
    (hP : ∀ i x, x ∈ P i → e i • x = x) : iSupIndep P := by
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  have hsum' := congrArg (fun x : N => e i • x) hsum
  simp only [Finset.smul_sum, smul_zero] at hsum'
  rw [Finset.sum_eq_single i] at hsum'
  · simpa only [hP i (v i) (hv i hi)] using hsum'
  · intro j hj hji
    calc
      e i • v j = e i • (e j • v j) :=
        congrArg (fun x : N => e i • x) (hP j (v j) (hv j hj)).symm
      _ = (e i * e j) • v j := (mul_smul ..).symm
      _ = 0 := by rw [he (Ne.symm hji), zero_smul]
  · intro h
    exact (h hi).elim

/-- The determinant components are independent, since their cutting idempotents are
orthogonal. -/
public theorem component_iSupIndep [Module.Finite R M] [Module.Projective R M] :
    iSupIndep (component (R := R) (M := M)) := by
  apply iSupIndep_of_orthogonal_idempotents
    (fun n => rankIdempotent (R := R) (M := M) n)
  · intro m n hmn
    exact rankIdempotent_mul_eq_zero_of_ne hmn
  · intro n x hx
    exact rankIdempotent_smul_eq_self_of_mem_component hx

/-- The determinant line is finite projective. -/
private theorem module_finite_projective [Module.Finite R M] [Module.Projective R M] :
    Module.Finite R (module (R := R) (M := M)) ∧
      Module.Projective R (module (R := R) (M := M)) := by
  classical
  have hfinite : Module.Finite R (module (R := R) (M := M)) := by
    obtain ⟨s, hs⟩ := exists_finset_rankLocus_cover (R := R) (M := M)
    have : ∀ n : s, Module.Finite R (component (R := R) (M := M) n.1) :=
      fun n => (component_finite_projective n.1).1
    change Module.Finite R (↥(submodule (R := R) (M := M)))
    rw [submodule_eq_iSup_finset_cover hs]
    infer_instance
  have hprojective : Module.Projective R (module (R := R) (M := M)) := by
    let F : (Π₀ n : ℕ, component (R := R) (M := M) n) →ₗ[R]
        ExteriorAlgebra R M :=
      DFinsupp.lsum ℕ (fun n => (component (R := R) (M := M) n).subtype)
    have hF : Function.Injective F :=
      (iSupIndep_iff_dfinsupp_lsum_injective _).mp
        (component_iSupIndep (R := R) (M := M))
    have hrange : F.range = submodule (R := R) (M := M) := by
      simpa only [F, submodule] using
        (Submodule.iSup_eq_range_dfinsupp_lsum
          (component (R := R) (M := M))).symm
    have : ∀ n : ℕ, Module.Projective R (component (R := R) (M := M) n) :=
      fun n => (component_finite_projective n).2
    change Module.Projective R (↥(submodule (R := R) (M := M)))
    rw [← hrange]
    exact Module.Projective.of_equiv' (LinearEquiv.ofInjective F hF)
  exact ⟨hfinite, hprojective⟩

private theorem exteriorAlgebra_baseChange_ιMulti {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M]
    (n : ℕ) (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A]
      A ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] (ExteriorAlgebra.ι R m)) (m : Fin n → M) :
    e (ExteriorAlgebra.ιMulti A n (fun i => 1 ⊗ₜ[R] m i)) =
      1 ⊗ₜ[R] (ExteriorAlgebra.ιMulti R n m) := by
  have hl (l : List M) :
      (l.map (fun x => (1 : A) ⊗ₜ[R] (ExteriorAlgebra.ι R x))).prod =
        ((1 : A) ⊗ₜ[R] (l.map (ExteriorAlgebra.ι R)).prod :
          A ⊗[R] ExteriorAlgebra R M) := by
    induction l with
    | nil => simp [Algebra.TensorProduct.one_def]
    | cons x xs ih => simp [ih, Algebra.TensorProduct.tmul_mul_tmul]
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod]
  simpa only [List.map_ofFn, Function.comp_def, he] using hl (List.ofFn m)

private theorem tensorProduct_span_one_tmul {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] :
    Submodule.span A (Set.range (TensorProduct.mk R A M 1)) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  suffices ∀ y : A ⊗[R] M,
      y ∈ Submodule.span A (Set.range (TensorProduct.mk R A M 1)) from this x
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      have h : (1 : A) ⊗ₜ[R] m ∈
          Submodule.span A (Set.range (TensorProduct.mk R A M 1)) :=
        Submodule.subset_span ⟨m, rfl⟩
      simpa [TensorProduct.smul_tmul'] using
        (Submodule.smul_mem (Submodule.span A _) a h)
  | add x y hx hy => exact Submodule.add_mem _ hx hy

private theorem exteriorPower_span_pure_baseChange {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] (n : ℕ) :
    Submodule.span A (Set.range (fun v : Fin n → M =>
      ExteriorAlgebra.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] v i))) =
        (⋀[A]^n (A ⊗[R] M)) := by
  have hs :
      Set.range (fun v : Fin n → M =>
        ExteriorAlgebra.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] v i)) =
      (ExteriorAlgebra.ιMulti A n) ''
        {a : Fin n → A ⊗[R] M | Set.range a ⊆
          Set.range (TensorProduct.mk R A M 1)} := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨fun i => (1 : A) ⊗ₜ[R] v i, ?_, rfl⟩
      intro y hy
      obtain ⟨i, rfl⟩ := hy
      exact ⟨v i, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      classical
      have h (i : Fin n) : ∃ m : M, (1 : A) ⊗ₜ[R] m = a i := ha ⟨i, rfl⟩
      choose v hv using h
      refine ⟨v, ?_⟩
      exact congrArg (ExteriorAlgebra.ιMulti A n) (funext hv)
  rw [hs]
  exact exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top
    (R := A) (M := A ⊗[R] M) (n := n)
    (tensorProduct_span_one_tmul (R := R) (A := A) (M := M))

private theorem exteriorPower_baseChange_grade_map {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M]
    (n : ℕ) (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A]
      A ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] (ExteriorAlgebra.ι R m)) :
    Submodule.map e.toLinearEquiv.toLinearMap (⋀[A]^n (A ⊗[R] M)) =
      Submodule.baseChange A (⋀[R]^n M) := by
  rw [← exteriorPower_span_pure_baseChange (R := R) (A := A) (M := M) n]
  rw [Submodule.map_span]
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree (R := R) (M := M) n,
    Submodule.baseChange_span]
  congr 1
  ext x
  constructor
  · rintro ⟨z, ⟨v, rfl⟩, rfl⟩
    refine ⟨ExteriorAlgebra.ιMulti R n v, ⟨v, rfl⟩, ?_⟩
    exact (exteriorAlgebra_baseChange_ιMulti n e he v).symm
  · rintro ⟨z, ⟨v, rfl⟩, rfl⟩
    refine ⟨ExteriorAlgebra.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] v i), ⟨v, rfl⟩, ?_⟩
    exact exteriorAlgebra_baseChange_ιMulti n e he v

/-- Flat base change of the `n`th exterior power, obtained by restricting the
exterior-algebra base-change equivalence to degree `n`. -/
private noncomputable def exteriorPower_baseChangeEquiv {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [AddCommGroup M] [Module R M]
    (n : ℕ) (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A]
      A ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] (ExteriorAlgebra.ι R m)) :
    (A ⊗[R] (⋀[R]^n M)) ≃ₗ[A] (⋀[A]^n (A ⊗[R] M)) :=
  (Submodule.toBaseChange.toLinearEquiv A (⋀[R]^n M)).trans
    ((e.toLinearEquiv.ofSubmodules (⋀[A]^n (A ⊗[R] M))
      (Submodule.baseChange A (⋀[R]^n M))
      (exteriorPower_baseChange_grade_map n e he)).symm)

/-- The exterior-power functor sends a linear equivalence to a linear equivalence. -/
private noncomputable def exteriorPower_mapEquiv {A P Q : Type*} [CommRing A]
    [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (n : ℕ) (e : P ≃ₗ[A] Q) : (⋀[A]^n P) ≃ₗ[A] (⋀[A]^n Q) := by
  let f := exteriorPower.map n e.toLinearMap
  have hi : Function.Injective f :=
    exteriorPower.map_injective e.symm.toLinearMap (by ext x; simp)
  have hs : Function.Surjective f := exteriorPower.map_surjective e.surjective
  exact LinearEquiv.ofBijective f ⟨hi, hs⟩

/-- The stalk rank of an exterior power is the binomial coefficient of the stalk rank. -/
@[ega "IV 16.6.5" "Count clause"]
private theorem exteriorPower_rankAtStalk {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (p : PrimeSpectrum R) :
    Module.rankAtStalk (⋀[R]^n M) p = (Module.rankAtStalk M p).choose n := by
  let S := p.asIdeal.primeCompl
  let A := Localization.AtPrime p.asIdeal
  let Q := LocalizedModule S M
  let W := ⋀[R]^n M
  let e := Classical.choose (ExteriorAlgebra.exists_algEquiv_baseChange R A M)
  have he := Classical.choose_spec (ExteriorAlgebra.exists_algEquiv_baseChange R A M)
  let eW : A ⊗[R] W ≃ₗ[A] ⋀[A]^n (A ⊗[R] M) := exteriorPower_baseChangeEquiv n e he
  let eM : A ⊗[R] M ≃ₗ[A] Q := (LocalizedModule.equivTensorProduct S M).symm
  let eQ : (⋀[A]^n (A ⊗[R] M)) ≃ₗ[A] ⋀[A]^n Q := exteriorPower_mapEquiv n eM
  let e' : LocalizedModule S W ≃ₗ[A] ⋀[A]^n Q :=
    (LocalizedModule.equivTensorProduct S W).trans (eW.trans eQ)
  let : Module.Free A Q := Module.free_of_flat_of_isLocalRing
  have : Module.Finite A Q := inferInstance
  have : Nontrivial A := inferInstance
  change Module.finrank A (LocalizedModule S W) =
    (Module.finrank A Q).choose n
  rw [e'.finrank_eq, exteriorPower.finrank_eq]

private theorem idempotent_localization_eq_zero_of_mem {R : Type*} [CommRing R]
    (e : R) (he : IsIdempotentElem e) (p : PrimeSpectrum R)
    (hp : e ∈ p.asIdeal) :
    (algebraMap R (Localization.AtPrime p.asIdeal)) e = 0 := by
    have hc : (1 - e : R) ∉ p.asIdeal := by
      intro hh
      have h1 : (1 : R) ∈ p.asIdeal := by
        convert p.asIdeal.add_mem hh hp using 1
        ring
      exact p.2.ne_top ((Ideal.eq_top_iff_one p.asIdeal).mpr h1)
    have hu : IsUnit ((algebraMap R (Localization.AtPrime p.asIdeal)) (1 - e)) :=
      IsLocalization.map_units (M := p.asIdeal.primeCompl) _
        ⟨1 - e, Ideal.mem_primeCompl_iff.mpr hc⟩
    have hz : e * (1 - e) = 0 := by
      calc
        e * (1 - e) = e - e * e := by ring
        _ = 0 := by rw [he]; ring
    have hza : (algebraMap R (Localization.AtPrime p.asIdeal)) e *
        (algebraMap R (Localization.AtPrime p.asIdeal)) (1 - e) = 0 := by
      rw [← map_mul, hz, map_zero]
    exact hu.mul_right_cancel (by simpa only [zero_mul] using hza)

private theorem idempotent_localization_eq_one_of_not_mem {R : Type*} [CommRing R]
    (e : R) (he : IsIdempotentElem e) (p : PrimeSpectrum R)
    (hp : e ∉ p.asIdeal) :
    (algebraMap R (Localization.AtPrime p.asIdeal)) e = 1 := by
    have hu : IsUnit ((algebraMap R (Localization.AtPrime p.asIdeal)) e) :=
      IsLocalization.map_units (M := p.asIdeal.primeCompl) _
        ⟨e, Ideal.mem_primeCompl_iff.mpr hp⟩
    have ha : IsIdempotentElem ((algebraMap R (Localization.AtPrime p.asIdeal)) e) := by
      change _ * _ = _
      rw [← map_mul, he]
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha

private theorem localizedModule_map_comp {R : Type*} [CommRing R]
    {S : Submonoid R} {N₁ N₂ N₃ : Type*}
    [AddCommGroup N₁] [Module R N₁]
    [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃) :
    (LocalizedModule.map S g).comp (LocalizedModule.map S f) =
      LocalizedModule.map S (g.comp f) := by
  ext x
  induction x using LocalizedModule.induction_on with
  | h m s => simp [LocalizedModule.map_mk]

private theorem localizedModule_map_smul_id {R N : Type*} [CommRing R]
    [AddCommGroup N] [Module R N] (S : Submonoid R) (e : R) :
    LocalizedModule.map S (e • (LinearMap.id : N →ₗ[R] N)) =
      (algebraMap R (Localization S)) e •
        (LinearMap.id : LocalizedModule S N →ₗ[Localization S] LocalizedModule S N) := by
  rw [map_smul, LocalizedModule.map_id]
  ext x
  simp [algebraMap_smul]

private theorem rankAtStalk_range_smul_id_of_not_mem {R N : Type*} [CommRing R]
    [AddCommGroup N] [Module R N] (e : R) (he : IsIdempotentElem e)
    (p : PrimeSpectrum R) (hp : e ∉ p.asIdeal) :
    Module.rankAtStalk (LinearMap.range (e • (LinearMap.id : N →ₗ[R] N))) p =
      Module.rankAtStalk N p := by
  let S := p.asIdeal.primeCompl
  let A := Localization.AtPrime p.asIdeal
  let f : N →ₗ[R] N := e • LinearMap.id
  let P := LinearMap.range f
  let q : N →ₗ[R] P := f.codRestrict P (fun x => ⟨x, rfl⟩)
  let i : P →ₗ[R] N := P.subtype
  let iq := LocalizedModule.map S i
  let qi := LocalizedModule.map S q
  have hi : Function.Injective iq :=
    LocalizedModule.map_injective S i (Submodule.subtype_injective P)
  have hcomp : iq.comp qi = LinearMap.id := by
    rw [localizedModule_map_comp q i]
    have hfi : i.comp q = f := rfl
    rw [hfi]
    change LocalizedModule.map S (e • LinearMap.id) = _
    rw [localizedModule_map_smul_id S e, idempotent_localization_eq_one_of_not_mem e he p hp]
    simp
  have hs : Function.Surjective iq := fun x => ⟨qi x, LinearMap.congr_fun hcomp x⟩
  let eqv : LocalizedModule S P ≃ₗ[A] LocalizedModule S N :=
    LinearEquiv.ofBijective iq ⟨hi, hs⟩
  exact eqv.finrank_eq

private theorem rankAtStalk_range_smul_id_of_mem {R N : Type*} [CommRing R]
    [AddCommGroup N] [Module R N] (e : R) (he : IsIdempotentElem e)
    (p : PrimeSpectrum R) (hp : e ∈ p.asIdeal) :
    Module.rankAtStalk (LinearMap.range (e • (LinearMap.id : N →ₗ[R] N))) p = 0 := by
  let S := p.asIdeal.primeCompl
  let A := Localization.AtPrime p.asIdeal
  let f : N →ₗ[R] N := e • LinearMap.id
  let P := LinearMap.range f
  let i : P →ₗ[R] N := P.subtype
  let iq := LocalizedModule.map S i
  have hi : Function.Injective iq :=
    LocalizedModule.map_injective S i (Submodule.subtype_injective P)
  have hfix : f.comp i = i := by
    ext x
    rcases x.2 with ⟨y, hy⟩
    change e • x.1 = x.1
    rw [← hy]
    change e • (e • y) = e • y
    rw [← mul_smul, he]
  have hcomp : (LocalizedModule.map S f).comp iq = iq := by
    rw [localizedModule_map_comp i f, hfix]
  have hz : LocalizedModule.map S f = 0 := by
    change LocalizedModule.map S (e • LinearMap.id) = 0
    rw [localizedModule_map_smul_id S e, idempotent_localization_eq_zero_of_mem e he p hp]
    simp
  have hzero (x : LocalizedModule S P) : iq x = 0 := by
    have hh := LinearMap.congr_fun hcomp x
    rw [hz] at hh
    simpa using hh.symm
  have hsub : Subsingleton (LocalizedModule S P) := by
    constructor
    intro x y
    apply hi
    rw [hzero x, hzero y]
  change Module.finrank A (LocalizedModule S P) = 0
  exact Module.finrank_zero_of_subsingleton

/-- A determinant rank component is the range of its idempotent on the
corresponding exterior power. -/
private noncomputable def componentEquivRange {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) :
    LinearMap.range ((ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n) •
      (LinearMap.id : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M))) ≃ₗ[R]
      ProjectiveDeterminant.component (R := R) (M := M) n := by
  let W := ⋀[R]^n M
  let e := ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n
  let f : W →ₗ[R] W := e • LinearMap.id
  let P := LinearMap.range f
  let j : W →ₗ[R] ExteriorAlgebra R M := W.subtype
  have hm (x : P) : j x.1 ∈ ProjectiveDeterminant.component (R := R) (M := M) n := by
    rcases x.2 with ⟨y, hy⟩
    rw [← hy]
    exact Submodule.mem_map.mpr ⟨j y, y.2, by simp [f, j, e]⟩
  let g : P →ₗ[R] ProjectiveDeterminant.component (R := R) (M := M) n :=
    (j.comp P.subtype).codRestrict _ hm
  have hgi : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Submodule.subtype_injective W
    have hv := congrArg Subtype.val h
    exact hv
  have hgs : Function.Surjective g := by
    intro x
    rcases Submodule.mem_map.mp x.2 with ⟨z, hz, hx⟩
    let w : W := ⟨z, hz⟩
    refine ⟨⟨f w, ⟨w, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact hx
  exact LinearEquiv.ofBijective g ⟨hgi, hgs⟩

set_option backward.isDefEq.respectTransparency false in
/-- A determinant component has stalk rank one on its own stratum and zero elsewhere. -/
private theorem component_rankAtStalk {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (p : PrimeSpectrum R) :
    Module.rankAtStalk (ProjectiveDeterminant.component (R := R) (M := M) n) p =
      if Module.rankAtStalk M p = n then 1 else 0 := by
  classical
  let e := ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n
  have he : IsIdempotentElem e :=
    (ProjectiveDeterminant.rankIdempotent_spec (R := R) (M := M) n).1
  have hcongr := congrFun (Module.rankAtStalk_eq_of_equiv
    (R := R)
    (M := ↥(LinearMap.range ((ProjectiveDeterminant.rankIdempotent
      (R := R) (M := M) n) •
        (LinearMap.id : (⋀[R]^n M) →ₗ[R] (⋀[R]^n M)))))
    (N := ProjectiveDeterminant.component (R := R) (M := M) n)
    (componentEquivRange (R := R) (M := M) n)) p
  split_ifs with hp
  · have he' : e ∉ p.asIdeal := by
      have hh : p ∈ ProjectiveDeterminant.rankLocus (R := R) M n := hp
      rw [(ProjectiveDeterminant.rankIdempotent_spec (R := R) (M := M) n).2] at hh
      exact hh
    rw [← hcongr, rankAtStalk_range_smul_id_of_not_mem e he p he', exteriorPower_rankAtStalk, hp,
      Nat.choose_self]
  · have he' : e ∈ p.asIdeal := by
      by_contra hh
      apply hp
      have hh' : p ∈ (PrimeSpectrum.basicOpen
          (ProjectiveDeterminant.rankIdempotent (R := R) (M := M) n) :
            Set (PrimeSpectrum R)) := hh
      rw [← (ProjectiveDeterminant.rankIdempotent_spec (R := R) (M := M) n).2] at hh'
      exact hh'
    rw [← hcongr, rankAtStalk_range_smul_id_of_mem e he p he']

/-- On a finite rank-stratum cover, the determinant module has stalk rank one. -/
private theorem module_rankAtStalk_eq_one_of_finite_cover {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (s : Finset ℕ)
    (hs : ProjectiveDeterminant.submodule (R := R) (M := M) =
      ⨆ n : s, ProjectiveDeterminant.component (R := R) (M := M) n)
    (hcover : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ n ∈ s, ProjectiveDeterminant.rankLocus (R := R) M n)
    (hf : ∀ n : s,
      Module.Finite R (ProjectiveDeterminant.component (R := R) (M := M) n) ∧
        Module.Projective R (ProjectiveDeterminant.component (R := R) (M := M) n))
    (hi : iSupIndep (fun n : s =>
      (ProjectiveDeterminant.component (R := R) (M := M) n).comap
        (ProjectiveDeterminant.submodule (R := R) (M := M)).subtype))
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (ProjectiveDeterminant.module (R := R) (M := M)) p = 1 := by
  classical
  let D := ProjectiveDeterminant.submodule (R := R) (M := M)
  let C : s → Submodule R D := fun n =>
    (ProjectiveDeterminant.component (R := R) (M := M) n).comap D.subtype
  have htop : (⨆ n : s, C n) = ⊤ := by
    have h' := Submodule.biSup_comap_subtype_eq_top (Set.univ : Set s)
      (fun n : s => ProjectiveDeterminant.component (R := R) (M := M) n)
    have hsup : (⨆ i ∈ (Set.univ : Set s),
        ProjectiveDeterminant.component (R := R) (M := M) i) =
        (⨆ i : s, ProjectiveDeterminant.component (R := R) (M := M) i) := by
      simp
    rw [hsup, ← hs] at h'
    simpa [C, D] using h'
  let eD : (Π₀ n : s, C n) ≃ₗ[R] D := hi.linearEquiv htop
  let eP : ((n : s) → C n) ≃ₗ[R] D := DFinsupp.linearEquivFunOnFintype.symm.trans eD
  let eqv (n : s) : C n ≃ₗ[R] ProjectiveDeterminant.component (R := R) (M := M) n :=
    Submodule.comapSubtypeEquivOfLe (ProjectiveDeterminant.component_le_submodule n)
  have : ∀ n : s, Module.Projective R (C n) := fun n => by
    let : Module.Projective R (ProjectiveDeterminant.component (R := R) (M := M) n) :=
      (hf n).2
    exact Module.Projective.of_equiv' (eqv n).symm
  have : ∀ n : s, Module.Flat R (C n) := fun _ => Module.Flat.of_projective
  have : ∀ n : s, Module.Finite R (C n) := fun n => by
    let : Module.Finite R (ProjectiveDeterminant.component (R := R) (M := M) n) :=
      (hf n).1
    exact Module.Finite.equiv (eqv n).symm
  have hsum := Module.rankAtStalk_pi (fun n : s => C n) p
  have hcongr : Module.rankAtStalk D p = Module.rankAtStalk ((n : s) → C n) p :=
    (congrFun (Module.rankAtStalk_eq_of_equiv (R := R) (M := ((n : s) → C n))
      (N := D) eP) p).symm
  rw [hcongr, hsum]
  let r := Module.rankAtStalk M p
  have hr : r ∈ s := by
    obtain ⟨m, hm, hpm⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_univ p))
    have hmr : m = r := hpm.symm
    exact hmr ▸ hm
  have hC (n : s) : Module.rankAtStalk (C n) p =
      if r = (n : ℕ) then 1 else 0 := by
    have h := congrFun (Module.rankAtStalk_eq_of_equiv
      (R := R) (M := C n)
      (N := ProjectiveDeterminant.component (R := R) (M := M) n) (eqv n)) p
    simpa only [component_rankAtStalk, r] using h
  simp_rw [hC]
  rw [finsum_eq_sum_of_fintype]
  have huniq : ∀ i j : s, r = (i : ℕ) → r = (j : ℕ) → i = j := by
    intro i j hi hj
    exact Subtype.ext (hi.symm.trans hj)
  rw [Fintype.sum_ite_eq_ite_exists (fun i : s => r = (i : ℕ)) huniq]
  simp [hr]

/-- The determinant line is finite locally free of rank one. -/
public theorem invertible [Module.Finite R M] [Module.Projective R M] :
    Module.Invertible R (module (R := R) (M := M)) := by
  let : Module.Finite R (module (R := R) (M := M)) := module_finite_projective.1
  let : Module.Projective R (module (R := R) (M := M)) := module_finite_projective.2
  obtain ⟨s, hs⟩ := exists_finset_rankLocus_cover (R := R) (M := M)
  have hsub := submodule_eq_iSup_finset_cover hs
  let D := submodule (R := R) (M := M)
  let C : s → Submodule R D := fun n =>
    (component (R := R) (M := M) n).comap D.subtype
  have hind : iSupIndep C := by
    apply iSupIndep_of_orthogonal_idempotents
      (fun n : s => rankIdempotent (R := R) (M := M) n) C
    · intro i j hij
      exact rankIdempotent_mul_eq_zero_of_ne (fun h => hij (Subtype.ext h))
    · intro i x hx
      apply Subtype.ext
      exact rankIdempotent_smul_eq_self_of_mem_component hx
  exact invertible_of_rankAtStalk_eq_one (fun p =>
    module_rankAtStalk_eq_one_of_finite_cover s hsub hs
      (fun n => component_finite_projective n) hind p)

end Invertibility

/-- At every prime the determinant line has rank one. -/
public theorem rankAtStalk_eq_one [Module.Finite R M] [Module.Projective R M]
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (module (R := R) (M := M)) p = 1 := by
  let := invertible (R := R) (M := M)
  exact Module.Invertible.finrank_eq_one _ _

end

end

end ProjectiveDeterminant
