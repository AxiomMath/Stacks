module

public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic.Det

/-!
# Localization of the determinant line

The determinant is compatible with localization; as consequences, the determinant line is the
annihilator of the degree-one part of the exterior algebra, and the determinant is unchanged when
the two factors of a composite are switched.

## Main results

* `ProjectiveDeterminant.det_localization`: compatibility with localization.
* `ProjectiveDeterminant.determinant_submodule_eq_annihilator`: the determinant line is the
  annihilator of the degree-one part in the exterior algebra.
* `ProjectiveDeterminant.det_one_add_comp_comm`: `det (1 + a ∘ b) = det (1 + b ∘ a)` for maps
  in opposite directions between finite projective modules.

## References

* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
* [Stacks Project, Tag 0FJF](https://stacks.math.columbia.edu/tag/0FJF)
-/

namespace ProjectiveDeterminant

section

universe u v w

@[expose] public section

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open scoped TensorProduct

section LocalExterior

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  (S : Submonoid R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]

private def localExteriorMap
    (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M) :
    ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra A (A ⊗[R] M) :=
  e.symm.toLinearEquiv.restrictScalars R ∘ₗ
    TensorProduct.mk R A (ExteriorAlgebra R M) 1

private lemma localExteriorMap_ι
    (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] ExteriorAlgebra.ι R m) (m : M) :
    localExteriorMap (R := R) (M := M) (A := A) e (ExteriorAlgebra.ι R m) =
      ExteriorAlgebra.ι A (1 ⊗ₜ[R] m) := by
  apply e.injective
  simpa [localExteriorMap] using (he m).symm

private lemma localExteriorMap_mul
    (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M)
    (x y : ExteriorAlgebra R M) :
    localExteriorMap (R := R) (M := M) (A := A) e (x * y) =
      localExteriorMap (R := R) (M := M) (A := A) e x *
        localExteriorMap (R := R) (M := M) (A := A) e y := by
  show e.symm (1 ⊗ₜ[R] (x * y)) = e.symm (1 ⊗ₜ[R] x) * e.symm (1 ⊗ₜ[R] y)
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

private lemma localExteriorMap_ιMulti
    (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] ExteriorAlgebra.ι R m) (n : ℕ) (v : Fin n → M) :
    localExteriorMap (R := R) (M := M) (A := A) e
      (ExteriorAlgebra.ιMulti R n v) =
      ExteriorAlgebra.ιMulti A n (fun i => 1 ⊗ₜ[R] v i) := by
  induction n with
  | zero =>
      simp [localExteriorMap, ExteriorAlgebra.ιMulti_zero_apply, Algebra.TensorProduct.one_def]
  | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply,
        localExteriorMap_mul (R := R) (M := M) (A := A),
        localExteriorMap_ι (R := R) (M := M) (A := A) e he,
        ih (Matrix.vecTail v), ExteriorAlgebra.ιMulti_succ_apply]
      rfl

private lemma pureTensor_span_eq_top :
    Submodule.span A (Set.range (fun m : M => (1 : A) ⊗ₜ[R] m)) = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  induction x using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | tmul a m =>
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨m, rfl⟩)
  | add x y hx hy => exact add_mem hx hy

private lemma localExteriorMap_exteriorPower
    (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] ExteriorAlgebra.ι R m) (n : ℕ)
    [IsLocalizedModule S (localExteriorMap (R := R) (M := M) (A := A) e)] :
    Submodule.localized' A S (localExteriorMap (R := R) (M := M) (A := A) e)
      (⋀[R]^n M) = ⋀[A]^n (A ⊗[R] M) := by
  classical
  let F := localExteriorMap (R := R) (M := M) (A := A) e
  rw [← exteriorPower.ιMulti_span_fixedDegree R n M,
    Submodule.localized'_span]
  have hset : F '' Set.range (ExteriorAlgebra.ιMulti R n) =
      ExteriorAlgebra.ιMulti A n ''
        {v : Fin n → A ⊗[R] M | Set.range v ⊆
          Set.range (fun m : M => (1 : A) ⊗ₜ[R] m)} := by
    ext x
    constructor
    · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
      refine ⟨fun i => (1 : A) ⊗ₜ[R] v i, ?_, ?_⟩
      · intro y hy
        obtain ⟨i, rfl⟩ := hy
        exact ⟨v i, rfl⟩
      · exact (localExteriorMap_ιMulti (R := R) (M := M) (A := A) e he n v).symm
    · rintro ⟨v, hv, rfl⟩
      have hchoose : ∀ i : Fin n, ∃ m : M, (1 : A) ⊗ₜ[R] m = v i := by
        intro i
        exact hv ⟨i, rfl⟩
      choose w hw using hchoose
      refine ⟨ExteriorAlgebra.ιMulti R n w, ⟨w, rfl⟩, ?_⟩
      rw [localExteriorMap_ιMulti (R := R) (M := M) (A := A) e he]
      congr 1
      funext i
      exact hw i
  rw [hset]
  exact exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top A n
    (A ⊗[R] M) (pureTensor_span_eq_top (R := R) (M := M) (A := A))

private lemma idempotent_eq_zero_or_one_of_isLocalRing
    {B : Type*} [CommRing B] [IsLocalRing B] {a : B}
    (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
  · exact Or.inr ((IsIdempotentElem.iff_eq_one_of_isUnit h).mp ha)
  · have h' : 1 - a = 1 :=
      (IsIdempotentElem.iff_eq_one_of_isUnit h).mp
        ((IsIdempotentElem.one_sub_iff).mpr ha)
    left
    exact sub_eq_self.mp h'

private theorem localExteriorMap_isLocalized
    (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M) :
    IsLocalizedModule S (localExteriorMap (R := R) (M := M) (A := A) e) := by
  let : IsLocalizedModule S (TensorProduct.mk R A (ExteriorAlgebra R M) 1) :=
    IsLocalization.tensorProduct_isLocalizedModule S A
  let E : (A ⊗[R] ExteriorAlgebra R M) ≃ₗ[R]
      ExteriorAlgebra A (A ⊗[R] M) := e.symm.toLinearEquiv.restrictScalars R
  have h := IsLocalizedModule.of_linearEquiv S
    (TensorProduct.mk R A (ExteriorAlgebra R M) 1) E
  exact h

end LocalExterior

attribute [local instance] localExteriorMap_isLocalized

private lemma rankIdempotent_map_atPrime
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (P : Ideal R) [P.IsPrime] (k : ℕ) :
    (algebraMap R (Localization.AtPrime P))
      (ProjectiveDeterminant.rankIdempotent (R := R) (M := M) k) =
      if Module.rankAtStalk M (⟨P, inferInstance⟩ : PrimeSpectrum R) = k
      then 1 else 0 := by
  let a := ProjectiveDeterminant.rankIdempotent (R := R) (M := M) k
  have ha : IsIdempotentElem a :=
    (ProjectiveDeterminant.rankIdempotent_spec (R := R) (M := M) k).1
  have hmap : IsIdempotentElem ((algebraMap R (Localization.AtPrime P)) a) :=
    ha.map _
  split_ifs with h
  · have hmem : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∈
        ProjectiveDeterminant.rankLocus (R := R) M k := h
    rw [(ProjectiveDeterminant.rankIdempotent_spec (R := R) (M := M) k).2] at hmem
    have hnot : a ∉ P := hmem
    have hu : IsUnit ((algebraMap R (Localization.AtPrime P)) a) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ P a).mpr hnot
    exact (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp hmap
  · have hnot : (⟨P, inferInstance⟩ : PrimeSpectrum R) ∉
        ProjectiveDeterminant.rankLocus (R := R) M k := h
    rw [(ProjectiveDeterminant.rankIdempotent_spec (R := R) (M := M) k).2] at hnot
    have hmem : a ∈ P := by simpa using hnot
    have hnu : ¬IsUnit ((algebraMap R (Localization.AtPrime P)) a) := by
      intro hu
      exact ((IsLocalization.AtPrime.isUnit_to_map_iff _ P a).mp hu) hmem
    rcases idempotent_eq_zero_or_one_of_isLocalRing hmap with hz | ho
    · exact hz
    · exact (hnu (ho ▸ isUnit_one)).elim
private lemma localized_map_smul_id_eq
    {R : Type u} [CommRing R] (S : Submonoid R) (A : Type u)
    [CommRing A] [Algebra R A] [IsLocalization S A]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type*} [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]
    (F : V →ₗ[R] W) [IsLocalizedModule S F]
    (U : Submodule R V) (r : R) (hr : (algebraMap R A) r = 1) :
    Submodule.localized' A S F (U.map (r • LinearMap.id)) =
      Submodule.localized' A S F U := by
  rw [Submodule.localized'_eq_span, Submodule.localized'_eq_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    refine ⟨z, hz, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [map_smul, ← algebraMap_smul A, hr, one_smul]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨r • y, Submodule.mem_map.mpr ⟨y, hy, by simp⟩, ?_⟩
    rw [map_smul, ← algebraMap_smul A, hr, one_smul]

private lemma localized_map_smul_id_eq_bot
    {R : Type u} [CommRing R] (S : Submonoid R) (A : Type u)
    [CommRing A] [Algebra R A] [IsLocalization S A]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type*} [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]
    (F : V →ₗ[R] W) [IsLocalizedModule S F]
    (U : Submodule R V) (r : R) (hr : (algebraMap R A) r = 0) :
    Submodule.localized' A S F (U.map (r • LinearMap.id)) = ⊥ := by
  rw [Submodule.localized'_eq_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    show F ((r • LinearMap.id) z) = 0
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [map_smul, ← algebraMap_smul A, hr, zero_smul]
  · exact bot_le
private lemma localExteriorMap_component_atPrime
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (P : Ideal R) [P.IsPrime]
    (e : ExteriorAlgebra (Localization.AtPrime P)
      ((Localization.AtPrime P) ⊗[R] M) ≃ₐ[Localization.AtPrime P]
        (Localization.AtPrime P) ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι (Localization.AtPrime P)
        (1 ⊗ₜ[R] m)) = 1 ⊗ₜ[R] ExteriorAlgebra.ι R m)
    (k : ℕ)
    [IsLocalizedModule P.primeCompl
      (localExteriorMap (R := R) (M := M) (A := Localization.AtPrime P) e)] :
    Submodule.localized' (Localization.AtPrime P) P.primeCompl
        (localExteriorMap (R := R) (M := M) (A := Localization.AtPrime P) e)
        (ProjectiveDeterminant.component (R := R) (M := M) k) =
      if Module.rankAtStalk M (⟨P, inferInstance⟩ : PrimeSpectrum R) = k
      then ⋀[Localization.AtPrime P]^k ((Localization.AtPrime P) ⊗[R] M)
      else ⊥ := by
  let A := Localization.AtPrime P
  let F := localExteriorMap (R := R) (M := M) (A := A) e
  show Submodule.localized' A P.primeCompl F
    ((⋀[R]^k M).map ((ProjectiveDeterminant.rankIdempotent (R := R) (M := M) k) •
      (LinearMap.id : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M))) = _
  by_cases h : Module.rankAtStalk M (⟨P, inferInstance⟩ : PrimeSpectrum R) = k
  · simp only [ite_eq_left h]
    rw [localized_map_smul_id_eq P.primeCompl A F _ _
      (by simpa [h] using rankIdempotent_map_atPrime (M := M) P k)]
    exact localExteriorMap_exteriorPower P.primeCompl A e he k
  · simp only [ite_eq_right h]
    exact localized_map_smul_id_eq_bot P.primeCompl A F _ _
      (by simpa [h] using rankIdempotent_map_atPrime (M := M) P k)
private lemma localExteriorMap_determinant_atPrime
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (P : Ideal R) [P.IsPrime]
    (e : ExteriorAlgebra (Localization.AtPrime P)
      ((Localization.AtPrime P) ⊗[R] M) ≃ₐ[Localization.AtPrime P]
        (Localization.AtPrime P) ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι (Localization.AtPrime P)
        (1 ⊗ₜ[R] m)) = 1 ⊗ₜ[R] ExteriorAlgebra.ι R m)
    [IsLocalizedModule P.primeCompl
      (localExteriorMap (R := R) (M := M) (A := Localization.AtPrime P) e)] :
    Submodule.localized' (Localization.AtPrime P) P.primeCompl
        (localExteriorMap (R := R) (M := M) (A := Localization.AtPrime P) e)
        (ProjectiveDeterminant.submodule (R := R) (M := M)) =
      ⋀[Localization.AtPrime P]^(Module.rankAtStalk M
          (⟨P, inferInstance⟩ : PrimeSpectrum R))
        ((Localization.AtPrime P) ⊗[R] M) := by
  let n := Module.rankAtStalk M (⟨P, inferInstance⟩ : PrimeSpectrum R)
  let A := Localization.AtPrime P
  let F := localExteriorMap (R := R) (M := M) (A := A) e
  show Submodule.localized' A P.primeCompl F
      (⨆ k, ProjectiveDeterminant.component (R := R) (M := M) k) = _
  rw [Submodule.localized'_iSup]
  apply le_antisymm
  · apply iSup_le
    intro k
    rw [localExteriorMap_component_atPrime P e he k]
    split_ifs with h
    · simp [h]
    · exact bot_le
  · have hle := le_iSup
      (fun k : ℕ => Submodule.localized' A P.primeCompl F
        (ProjectiveDeterminant.component (R := R) (M := M) k)) n
    rw [localExteriorMap_component_atPrime P e he n, ite_eq_left rfl] at hle
    exact hle

private lemma localExteriorMap_map
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {A : Type u} [CommRing A] [Algebra R A]
    (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] ExteriorAlgebra.ι R m)
    (f : M →ₗ[R] M) (x : ExteriorAlgebra R M) :
    localExteriorMap (R := R) (M := M) (A := A) e (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map (f.baseChange A)
        (localExteriorMap (R := R) (M := M) (A := A) e x) := by
  induction x using ExteriorAlgebra.induction with
  | algebraMap r =>
      have ht : (1 : A) ⊗ₜ[R] (algebraMap R (ExteriorAlgebra R M)) r =
          algebraMap A (A ⊗[R] ExteriorAlgebra R M) ((algebraMap R A) r) := by
        simpa [Algebra.TensorProduct.algebraMap_apply, Algebra.smul_def] using
          (TensorProduct.smul_tmul (r := r) (m := (1 : A))
            (n := (1 : ExteriorAlgebra R M))).symm
      simp only [localExteriorMap, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe, AlgHom.commutes, TensorProduct.mk_apply]
      rw [ht]
      show e.symm (algebraMap A (A ⊗[R] ExteriorAlgebra R M) ((algebraMap R A) r)) =
        ExteriorAlgebra.map (f.baseChange A)
          (e.symm (algebraMap A (A ⊗[R] ExteriorAlgebra R M) ((algebraMap R A) r)))
      rw [e.symm.commutes, (ExteriorAlgebra.map (f.baseChange A)).commutes]
  | ι m =>
      simp [ExteriorAlgebra.map_apply_ι,
        localExteriorMap_ι (R := R) (M := M) (A := A) e he,
        LinearMap.baseChange_tmul]
  | mul x y hx hy =>
      simp [localExteriorMap_mul, hx, hy]
  | add x y hx hy =>
      simp [hx, hy]
/-- The scalar determinant commutes with base change to the local ring at a prime. -/
public theorem det_baseChange_atPrime
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (P : Ideal R) [P.IsPrime] (f : M →ₗ[R] M) :
    algebraMap R (Localization.AtPrime P) (det f) =
      det (f.baseChange (Localization.AtPrime P)) := by
  classical
  let A := Localization.AtPrime P
  let Q := A ⊗[R] M
  let : Module.Free A Q := Module.free_of_flat_of_isLocalRing
  obtain ⟨e, he⟩ := ExteriorAlgebra.exists_algEquiv_baseChange R A M
  let F := localExteriorMap (R := R) (M := M) (A := A) e
  have hsub : Submodule.localized' A P.primeCompl F
      (submodule (R := R) (M := M)) = submodule (R := A) (M := Q) := by
    rw [localExteriorMap_determinant_atPrime P e he,
      submodule_eq_exteriorPower_of_free]
    congr 1
    exact (LocalizedModule.equivTensorProduct P.primeCompl M).finrank_eq
  apply (Classical.choose_spec (existsUnique_scalar
    (M := Q) (map (fun _ => rfl) (f.baseChange A)))).2
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  show ExteriorAlgebra.map (f.baseChange A) x.val =
    (algebraMap R A) (det f) • x.val
  have hx : x.val ∈ Submodule.span A (F '' submodule (R := R) (M := M)) := by
    rw [← Submodule.localized'_eq_span A P.primeCompl F, hsub]
    exact x.property
  refine Submodule.span_induction (p := fun y _ =>
    ExteriorAlgebra.map (f.baseChange A) y = (algebraMap R A) (det f) • y)
    ?_ ?_ ?_ ?_ hx
  · rintro y ⟨z, hz, rfl⟩
    have hdet := LinearMap.congr_fun
      (Classical.choose_spec (existsUnique_scalar
        (M := M) (map (fun _ => rfl) f))).1 ⟨z, hz⟩
    have hz' : ExteriorAlgebra.map f z = det f • z := congrArg Subtype.val hdet
    rw [← localExteriorMap_map e he f z, hz', map_smul, algebraMap_smul]
  · simp
  · intro x y hx hy ihx ihy
    simp [ihx, ihy, smul_add]
  · intro a x hx ih
    rw [map_smul, ih, smul_comm]

/-- Localizing an endomorphism of a finite projective module localizes its scalar determinant.
The localized module is finite free since the localization ring is local. -/
public theorem det_localization
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (P : Ideal R) [P.IsPrime] (f : M →ₗ[R] M) :
    letI : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
      Module.free_of_flat_of_isLocalRing
    algebraMap R (Localization.AtPrime P) (det f) =
      det (LocalizedModule.map P.primeCompl f) := by
  classical
  let A := Localization.AtPrime P
  let Q := LocalizedModule P.primeCompl M
  let : Module.Free A Q := Module.free_of_flat_of_isLocalRing
  let : Module.Free A (A ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  let e : Q ≃ₗ[A] A ⊗[R] M := LocalizedModule.equivTensorProduct P.primeCompl M
  have hconj : f.baseChange A = e.toLinearMap ∘ₗ
      LocalizedModule.map P.primeCompl f ∘ₗ e.symm.toLinearMap := by
    apply LinearMap.restrictScalars_injective R
    ext a m
    show f.baseChange A (a ⊗ₜ[R] m) =
      e (LocalizedModule.map P.primeCompl f (e.symm (a ⊗ₜ[R] m)))
    rw [TensorProduct.tmul_eq_smul_one_tmul]
    simp only [map_smul, LinearMap.baseChange_tmul]
    rw [show e.symm (1 ⊗ₜ[R] m) = LocalizedModule.mk m 1 from
      LocalizedModule.equivTensorProduct_symm_apply_tmul_one P.primeCompl m,
      LocalizedModule.map_mk]
    rw [show e (LocalizedModule.mk (f m) 1) =
        Localization.mk 1 (1 : P.primeCompl) ⊗ₜ[R] f m from
      LocalizedModule.equivTensorProduct_apply_mk P.primeCompl (f m) 1]
    simp only [Localization.mk_one, TensorProduct.smul_tmul']
  rw [det_baseChange_atPrime P f,
    det_eq_linearMap_det_of_basis (Module.finBasis A (A ⊗[R] M)),
    det_eq_linearMap_det_of_basis (Module.finBasis A Q), hconj,
    LinearMap.det_conj]

end

end

/-! ### The determinant line as an exterior annihilator -/

section

universe u v

open scoped ExteriorAlgebra TensorProduct

private theorem exteriorPower_eq_common_kernel_of_finBasis {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}
    (b : Module.Basis (Fin n) R M) :
    (⋀[R]^n M) = ⨅ i : Fin n,
      LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R (b i))) := by
  classical
  let B := b.ExteriorAlgebra
  have hvanish (k : ℕ) (hk : n < k) : (⋀[R]^k M) = ⊥ := by
    let : Subsingleton (⋀[R]^k M) :=
      exteriorPower.subsingleton_of_span_eq_top_of_card_lt b b.span_eq k (by simpa using hk)
    ext x
    constructor
    · intro hx
      have hz : (⟨x, hx⟩ : ⋀[R]^k M) = 0 := Subsingleton.elim _ _
      exact congrArg Subtype.val hz
    · intro hx
      rw [Submodule.mem_bot] at hx
      subst x
      exact zero_mem _
  have haux : ∀ k : ℕ, ∀ (g : Fin k → M) (d : Fin k → Module.Dual R M),
      (∀ i j, d i (g j) = if i = j then 1 else 0) →
      ∀ x : ExteriorAlgebra R M, (∀ i : Fin k, ExteriorAlgebra.ι R (g i) * x = 0) →
        x ∈ (Submodule.span R (Set.range fun i : Fin k => ExteriorAlgebra.ι R (g i))) ^ k * ⊤ := by
    intro k
    induction k with
    | zero =>
        intro g d hdual x hx
        simp
    | succ k ih =>
        intro g d hdual x hx
        let d0 : Module.Dual R M := d 0
        let y : ExteriorAlgebra R M := CliffordAlgebra.contractLeft d0 x
        have hx0 : ExteriorAlgebra.ι R (g 0) * x = 0 := hx 0
        have hcontract0 := congrArg (CliffordAlgebra.contractLeft d0) hx0
        rw [CliffordAlgebra.contractLeft_ι_mul] at hcontract0
        have hxy : x = ExteriorAlgebra.ι R (g 0) * y := by
          have hsub : x - ExteriorAlgebra.ι R (g 0) * y = 0 := by
            simpa [y, d0, hdual 0 0] using hcontract0
          exact sub_eq_zero.mp hsub
        have hy : ∀ i : Fin k,
            ExteriorAlgebra.ι R (g i.succ) * y = 0 := by
          intro i
          have hxi : ExteriorAlgebra.ι R (g i.succ) * x = 0 := hx (Fin.succ i)
          have hcontracti := congrArg (CliffordAlgebra.contractLeft d0) hxi
          rw [CliffordAlgebra.contractLeft_ι_mul] at hcontracti
          have hne : (0 : Fin (k + 1)) ≠ i.succ := by
            intro h
            exact Fin.succ_ne_zero i h.symm
          have hcoord : d0 (g i.succ) = 0 := by
            simpa [d0, hne] using hdual 0 i.succ
          have hneg : -(ExteriorAlgebra.ι R (g i.succ) * y) = 0 := by
            simpa [y, d0, hcoord] using hcontracti
          exact neg_eq_zero.mp hneg
        have hydual : ∀ i j : Fin k, d i.succ (g j.succ) = if i = j then 1 else 0 := by
          intro i j
          simpa using hdual i.succ j.succ
        have hyk := ih (fun i => g i.succ) (fun i => d i.succ) hydual y hy
        let A := Submodule.span R (Set.range fun i : Fin (k + 1) => ExteriorAlgebra.ι R (g i))
        have htail :
            Submodule.span R (Set.range fun i : Fin k => ExteriorAlgebra.ι R (g i.succ)) ≤ A := by
          apply Submodule.span_mono
          rintro _ ⟨i, rfl⟩
          exact ⟨i.succ, rfl⟩
        have hpow :
            (Submodule.span R (Set.range fun i : Fin k => ExteriorAlgebra.ι R (g i.succ))) ^ k ≤ A ^
              k := by
          let C := Submodule.span R
            (Set.range fun i : Fin k => ExteriorAlgebra.ι R (g i.succ))
          have hp : ∀ j : ℕ, C ^ j ≤ A ^ j := by
            intro j
            induction j with
            | zero => exact le_rfl
            | succ j ihpow =>
              rw [Submodule.pow_succ, Submodule.pow_succ]
              apply Submodule.mul_le.2
              intro a ha b hb
              exact Submodule.mul_mem_mul (ihpow ha) (htail hb)
          exact hp k
        have hprodmono :
            (Submodule.span R (Set.range fun i : Fin k => ExteriorAlgebra.ι R (g i.succ))) ^ k * ⊤ ≤
              A ^ k * ⊤ := by
          apply Submodule.mul_le.2
          intro a ha b hb
          exact Submodule.mul_mem_mul (hpow ha) hb
        have hy' : y ∈ A ^ k * (⊤ : Submodule R (ExteriorAlgebra R M)) :=
          hprodmono hyk
        have hgen : ExteriorAlgebra.ι R (g 0) ∈ A :=
          Submodule.subset_span ⟨0, rfl⟩
        have hmem : ExteriorAlgebra.ι R (g 0) * y ∈ A * (A ^ k * ⊤) :=
          Submodule.mul_mem_mul hgen hy'
        have hmem' : ExteriorAlgebra.ι R (g 0) * y ∈ A ^ (k + 1) * ⊤ := by
          rw [pow_succ']
          rw [mul_assoc]
          exact hmem
        rw [hxy]
        exact hmem'
  ext x
  constructor
  · intro hx
    apply (Submodule.mem_iInf _).2
    intro i
    apply LinearMap.mem_ker.mpr
    show ExteriorAlgebra.ι R (b i) * x = 0
    have hmul : ExteriorAlgebra.ι R (b i) * x ∈ ⋀[R]^(n + 1) M := by
      rw [show (⋀[R]^(n + 1) M) =
        (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)) *
          (⋀[R]^n M) from pow_succ' _ _]
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) hx
    rw [hvanish (n + 1) (by omega)] at hmul
    exact hmul
  · intro hx
    have hx' : ∀ i : Fin n, ExteriorAlgebra.ι R (b i) * x = 0 := by
      intro i
      have hi := (Submodule.mem_iInf _).1 hx i
      simpa only [LinearMap.mem_ker, LinearMap.mulLeft_apply] using hi
    have hdual : ∀ i j : Fin n, b.coord i (b j) = if i = j then 1 else 0 := by
      intro i j
      rw [Module.Basis.coord_apply]
      simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
    have hspan :
        Submodule.span R (Set.range fun i : Fin n => ExteriorAlgebra.ι R (b i)) =
          LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact LinearMap.mem_range_self _ _
      · rintro _ ⟨m, rfl⟩
        rw [← b.sum_repr m, map_sum]
        exact Submodule.sum_mem _ fun i _ => by
          rw [map_smul]
          exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hprod := haux n b b.coord hdual x hx'
    have hprod_le :
        (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)) ^ n * ⊤ ≤
          ⋀[R]^n M := by
      rw [← ExteriorAlgebra.ιMulti_span (R := R) (M := M)]
      apply Submodule.mul_le.2
      intro a ha z hz
      refine Submodule.span_induction (p := fun z _ => a * z ∈ ⋀[R]^n M) ?_ ?_ ?_ ?_ hz
      · rintro _ ⟨⟨k, v⟩, rfl⟩
        have hmem : a * ExteriorAlgebra.ιMulti R k v ∈ ⋀[R]^(n + k) M := by
          rw [ExteriorAlgebra.exteriorPower, pow_add]
          exact Submodule.mul_mem_mul ha (ExteriorAlgebra.ιMulti_range R k ⟨v, rfl⟩)
        by_cases hk : k = 0
        · simpa [hk] using hmem
        · have hvan := hvanish (n + k) (by omega)
          rw [hvan, Submodule.mem_bot] at hmem
          rw [hmem]
          exact zero_mem _
      · simp
      · intro x y _ _ hx hy
        simpa [mul_add] using add_mem hx hy
      · intro r x _ hx
        simpa [smul_mul_assoc] using Submodule.smul_mem _ r hx
    have hxpower :
        x ∈ (LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)) ^ n * ⊤ := by
      simpa [hspan] using hprod
    exact hprod_le hxpower

section LocalExterior

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  (S : Submonoid R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]

end LocalExterior

attribute [local instance] localExteriorMap_isLocalized

private lemma localized_iInf_fin
    {R : Type u} [CommRing R] (S : Submonoid R) (A : Type u)
    [CommRing A] [Algebra R A] [IsLocalization S A]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type*} [AddCommGroup W] [Module R W] [Module A W] [IsScalarTower R A W]
    (f : V →ₗ[R] W) [IsLocalizedModule S f]
    {n : ℕ} (g : Fin n → Submodule R V) :
    Submodule.localized' A S f (⨅ i, g i) =
      ⨅ i, Submodule.localized' A S f (g i) := by
  classical
  have h : ∀ s : Finset (Fin n),
      Submodule.localized' A S f (s.inf g) =
        s.inf (fun i => Submodule.localized' A S f (g i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Submodule.localized'_top]
    | @insert i s his ih =>
        simp only [Finset.inf_insert, Submodule.localized'_inf, ih]
  simpa only [Finset.inf_univ_eq_iInf] using h Finset.univ
private lemma localExteriorMap_ker_mulLeft
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (S : Submonoid R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]
    (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] ExteriorAlgebra.ι R m) (m : M)
    [IsLocalizedModule S (localExteriorMap (R := R) (M := M) (A := A) e)] :
    Submodule.localized' A S (localExteriorMap (R := R) (M := M) (A := A) e)
      (LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))) =
    LinearMap.ker (LinearMap.mulLeft A (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m))) := by
  let F := localExteriorMap (R := R) (M := M) (A := A) e
  rw [LinearMap.localized'_ker_eq_ker_localizedMap A S F F]
  congr 1
  have hR :
      ((IsLocalizedModule.map S F F (LinearMap.mulLeft R (ExteriorAlgebra.ι R
        m))).extendScalarsOfIsLocalization S A).restrictScalars R =
        (LinearMap.mulLeft A (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m))).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext S F F
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.extendScalarsOfIsLocalization_apply', IsLocalizedModule.map_apply,
      LinearMap.mulLeft_apply]
    rw [localExteriorMap_mul (R := R) (M := M) (A := A),
      localExteriorMap_ι (R := R) (M := M) (A := A) e he]
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hR x
private lemma commonKernel_eq_basisKernel
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {n : ℕ} (g : Fin n → M) (hg : Submodule.span R (Set.range g) = ⊤) :
    (⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))) =
      ⨅ i : Fin n, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R (g i))) := by
  let K (x : ExteriorAlgebra R M) : Submodule R M :=
    LinearMap.ker ((LinearMap.mulRight R x).comp (ExteriorAlgebra.ι R))
  apply le_antisymm
  · exact le_iInf fun i => iInf_le _ (g i)
  · intro x hx
    apply (Submodule.mem_iInf _).2
    intro m
    have hgen : Submodule.span R (Set.range g) ≤ K x := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hi := (Submodule.mem_iInf _).mp hx i
      simpa [K, LinearMap.mem_ker] using hi
    have hm : m ∈ K x := hgen (by rw [hg]; trivial)
    simpa [K, LinearMap.mem_ker] using hm
private lemma pureTensor_span_generators
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (S : Submonoid R) (A : Type u) [CommRing A] [Algebra R A]
    [IsLocalization S A] {n : ℕ} (g : Fin n → M)
    (hg : Submodule.span R (Set.range g) = ⊤) :
    Submodule.span A (Set.range (fun i : Fin n => (1 : A) ⊗ₜ[R] g i)) = ⊤ := by
  let f : M →ₗ[R] A ⊗[R] M := TensorProduct.mk R A M 1
  have : IsLocalizedModule S f := IsLocalization.tensorProduct_isLocalizedModule S A
  have hh := congrArg (Submodule.localized' A S f) hg
  rw [Submodule.localized'_span, Submodule.localized'_top] at hh
  rw [← Set.range_comp] at hh
  simpa [f, Function.comp_def] using hh

private lemma localExteriorMap_commonKernel
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (S : Submonoid R) (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]
    (e : ExteriorAlgebra A (A ⊗[R] M) ≃ₐ[A] A ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι A (1 ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] ExteriorAlgebra.ι R m)
    [IsLocalizedModule S (localExteriorMap (R := R) (M := M) (A := A) e)] :
    Submodule.localized' A S (localExteriorMap (R := R) (M := M) (A := A) e)
      (⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))) =
    ⨅ z : A ⊗[R] M,
      LinearMap.ker (LinearMap.mulLeft A (ExteriorAlgebra.ι A z)) := by
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [commonKernel_eq_basisKernel g hg,
    localized_iInf_fin S A (localExteriorMap (R := R) (M := M) (A := A) e),
    commonKernel_eq_basisKernel
      (fun i : Fin n => (1 : A) ⊗ₜ[R] g i)
      (pureTensor_span_generators S A g hg)]
  congr 1
  funext i
  exact localExteriorMap_ker_mulLeft S A e he (g i)
private lemma localExteriorMap_main_atPrime
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    (P : Ideal R) [P.IsMaximal]
    (e : ExteriorAlgebra (Localization.AtPrime P)
      ((Localization.AtPrime P) ⊗[R] M) ≃ₐ[Localization.AtPrime P]
        (Localization.AtPrime P) ⊗[R] ExteriorAlgebra R M)
    (he : ∀ m : M, e (ExteriorAlgebra.ι (Localization.AtPrime P)
        (1 ⊗ₜ[R] m)) = 1 ⊗ₜ[R] ExteriorAlgebra.ι R m)
    [IsLocalizedModule P.primeCompl
      (localExteriorMap (R := R) (M := M) (A := Localization.AtPrime P) e)] :
    Submodule.localized' (Localization.AtPrime P) P.primeCompl
        (localExteriorMap (R := R) (M := M) (A := Localization.AtPrime P) e)
        (ProjectiveDeterminant.submodule (R := R) (M := M)) =
    Submodule.localized' (Localization.AtPrime P) P.primeCompl
        (localExteriorMap (R := R) (M := M) (A := Localization.AtPrime P) e)
        (⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))) := by
  let A := Localization.AtPrime P
  let N := A ⊗[R] M
  let f : M →ₗ[R] N := TensorProduct.mk R A M 1
  let : IsLocalizedModule P.primeCompl f :=
    IsLocalization.tensorProduct_isLocalizedModule P.primeCompl A
  let : Module.Flat R M := Module.Flat.of_projective
  let : Module.Finite A N := Module.Finite.of_isLocalizedModule P.primeCompl f
  let : Module.Flat A N := Module.Flat.of_isLocalizedModule A P.primeCompl f
  let : Module.Free A N := Module.free_of_flat_of_isLocalRing
  let n := Module.finrank A N
  let b : Module.Basis (Fin n) A N := Module.finBasis A N
  have hn : Module.rankAtStalk M (⟨P, inferInstance⟩ : PrimeSpectrum R) = n :=
    Module.rankAtStalk_eq_finrank_tensorProduct _
  rw [localExteriorMap_determinant_atPrime P e he,
    localExteriorMap_commonKernel P.primeCompl A e he, hn]
  exact (exteriorPower_eq_common_kernel_of_finBasis b).trans
    (commonKernel_eq_basisKernel b b.span_eq).symm
/-- **Stacks 0FJA.** The determinant line of a finite projective module is the
annihilator of the degree-one elements in its exterior algebra. -/
@[stacks 0FJA]
public theorem determinant_submodule_eq_annihilator (R : Type u) (M : Type v)
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ProjectiveDeterminant.submodule (R := R) (M := M) =
      ⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m))
    := by
  classical
  let A (P : Ideal R) [P.IsMaximal] := Localization.AtPrime P
  let E (P : Ideal R) [P.IsMaximal] :
      ExteriorAlgebra (A P) ((A P) ⊗[R] M) ≃ₐ[A P]
        (A P) ⊗[R] ExteriorAlgebra R M :=
    Classical.choose (ExteriorAlgebra.exists_algEquiv_baseChange R (A P) M)
  have hE (P : Ideal R) [P.IsMaximal] :
      ∀ m : M, E P (ExteriorAlgebra.ι (A P) (1 ⊗ₜ[R] m)) =
        1 ⊗ₜ[R] ExteriorAlgebra.ι R m :=
    Classical.choose_spec (ExteriorAlgebra.exists_algEquiv_baseChange R (A P) M)
  let F (P : Ideal R) [P.IsMaximal] :
      ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra (A P) ((A P) ⊗[R] M) :=
    localExteriorMap (R := R) (M := M) (A := A P) (E P)
  let : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (F P) :=
    fun P _ => localExteriorMap_isLocalized P.primeCompl (A P) (E P)
  apply Submodule.eq_of_localization_maximal A
    (fun P [P.IsMaximal] => ExteriorAlgebra (A P) ((A P) ⊗[R] M)) F
  intro P hP
  exact localExteriorMap_main_atPrime P (E P) (hE P)

end

/-! ### Switching the factors of a composite -/

section

universe u v w

/-- Localizing `1 + a ∘ b` gives `1 + (a localized) ∘ (b localized)`. -/
private theorem localizedModule_map_id_add_comp {R : Type u} [CommRing R] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N]
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    LocalizedModule.map S (LinearMap.id + a.comp b) =
      LinearMap.id + (LocalizedModule.map S a).comp (LocalizedModule.map S b) := by
  simp only [map_add, LocalizedModule.map_id]
  apply congrArg (fun f => LinearMap.id + f)
  apply LinearMap.ext
  intro x
  induction x with
  | _ x s =>
    simp only [LinearMap.comp_apply]
    rw [LocalizedModule.map_mk S (a.comp b) x s,
      LocalizedModule.map_mk S b x s, LocalizedModule.map_mk S a (b x) s]
    rfl

/-- **Stacks 0FJF.** For maps in opposite directions between finite projective modules, the
determinants of the identity plus the two possible composites agree. -/
@[stacks 0FJF]
public theorem det_one_add_comp_comm
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    ProjectiveDeterminant.det (LinearMap.id + a.comp b) =
      ProjectiveDeterminant.det (LinearMap.id + b.comp a)
    := by
  apply sub_eq_zero.mp
  apply eq_zero_of_localization
  intro P hP
  let : P.IsPrime := hP.isPrime
  let S := P.primeCompl
  let A := Localization.AtPrime P
  let MP := LocalizedModule S M
  let NP := LocalizedModule S N
  let : Module.Free A MP := Module.free_of_flat_of_isLocalRing
  let : Module.Free A NP := Module.free_of_flat_of_isLocalRing
  let aP : MP →ₗ[A] NP := LocalizedModule.map S a
  let bP : NP →ₗ[A] MP := LocalizedModule.map S b
  rw [map_sub, ProjectiveDeterminant.det_localization P,
    ProjectiveDeterminant.det_localization P]
  have ha := localizedModule_map_id_add_comp S a b
  have hb := localizedModule_map_id_add_comp S b a
  rw [ha, hb, ProjectiveDeterminant.det_one_add_comp_comm_of_basis
    (Module.finBasis A MP) (Module.finBasis A NP) aP bP]
  exact sub_self _

end

end ProjectiveDeterminant
