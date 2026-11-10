module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Norm.Defs
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The norm of a finite projective algebra

Let `R` be a commutative ring and `A` a commutative `R`-algebra which is finite and projective
as an `R`-module. Multiplication by `a : A` is an `R`-linear endomorphism of `A`, and the
scalar determinant `ProjectiveDeterminant.det` of that endomorphism is the *norm* of `a`.

When `A` is finite free over `R` this is `Algebra.norm`.

## Main definitions

* `Algebra.projectiveNorm`: the norm `A →* R` of a finite projective `R`-algebra.

## Main results

* `Algebra.projectiveNorm_eq_norm_of_free`: it agrees with `Algebra.norm` on a finite free
  algebra.
* `Algebra.projectiveNorm_baseChange` and `Algebra.projectiveNorm_pushout`: compatibility with
  base change, in the tensor-product form and in the form of an arbitrary pushout square of
  commutative rings.
* `Algebra.projectiveNorm_algebraMap_of_rankAtStalk`: the norm of a scalar is its `d`-th power,
  when `A` has constant rank `d`.
* `Algebra.projectiveNorm_eq_zero_of_field_hom`: the norm of an element vanishing at a point of
  `Spec A` vanishes at its image in `Spec R`.
* `ProjectiveDeterminant.det_baseChange`, `ProjectiveDeterminant.det_conj`,
  `ProjectiveDeterminant.det_smul_id_of_rankAtStalk`: the scalar determinant commutes with base
  change, is invariant under conjugation, and is `r ^ d` on `r • id` in constant rank `d`.
* `Module.rankAtStalk_eq_of_isFiniteLocallyFreeOfRank` and
  `Module.finite_and_projective_of_isFiniteLocallyFree`: a locally free module of constant rank
  `d` has `rankAtStalk` identically `d`, and a finite locally free module is finite
  projective.

## References

* [Stacks Project, Tag 0BD2](https://stacks.math.columbia.edu/tag/0BD2)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u

namespace ProjectiveDeterminant

/-- The scalar determinant of the identity is `1`. -/
theorem det_id {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ProjectiveDeterminant.det (LinearMap.id : M →ₗ[R] M) = 1 := by
  classical
  unfold ProjectiveDeterminant.det
  have hid : ProjectiveDeterminant.map (fun _ => rfl) (LinearMap.id : M →ₗ[R] M) =
      (1 : R) • LinearMap.id := by
    ext x
    simp [ProjectiveDeterminant.map]
  exact ((Classical.choose_spec (ProjectiveDeterminant.existsUnique_scalar
    (M := M) (ProjectiveDeterminant.map (fun _ => rfl) (LinearMap.id : M →ₗ[R] M)))).2
      1 hid).symm

/-- If `M` is a direct summand of a finite free module `F` by `s ∘ i = id`,
the scalar determinant of `f` is the ordinary determinant of `id + i ∘ (f - id) ∘ s`. -/
theorem det_stabilize {R M F : Type u}
    [CommRing R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
    (s : F →ₗ[R] M) (i : M →ₗ[R] F) (hi : s.comp i = LinearMap.id)
    (f : M →ₗ[R] M) :
    ProjectiveDeterminant.det f =
      LinearMap.det (LinearMap.id + i.comp ((f - LinearMap.id).comp s)) := by
  let b := (f - LinearMap.id).comp s
  have heq : LinearMap.id + b.comp i = f := by
    dsimp [b]
    rw [LinearMap.comp_assoc, hi, LinearMap.comp_id]
    abel
  calc
    ProjectiveDeterminant.det f =
        ProjectiveDeterminant.det (LinearMap.id + b.comp i) := by rw [heq]
    _ = ProjectiveDeterminant.det (LinearMap.id + i.comp b) :=
      ProjectiveDeterminant.det_one_add_comp_comm b i
    _ = LinearMap.det (LinearMap.id + i.comp b) :=
      ProjectiveDeterminant.det_eq_linearMap_det_of_basis (Module.finBasis R F) _

/-- A finite projective module is a retract of a finite free module `Fin n → R`. -/
private theorem exists_fin_split (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (s : (Fin n → R) →ₗ[R] M) (i : M →ₗ[R] (Fin n → R)), s.comp i = LinearMap.id := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  obtain ⟨n, _, s, _, hs, _⟩ := Module.FinitePresentation.exists_fin' R M
  obtain ⟨i, hi⟩ := (Module.Projective.iff_split_of_projective s hs).mp inferInstance
  exact ⟨n, s, i, hi⟩

/-- The scalar determinant commutes with base change along `R → A`. -/
theorem det_baseChange {R M A : Type u}
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    [CommRing A] [Algebra R A] (f : M →ₗ[R] M) :
    algebraMap R A (ProjectiveDeterminant.det f) =
      ProjectiveDeterminant.det (f.baseChange A) := by
  classical
  by_cases hA : Subsingleton A
  · let := hA
    exact Subsingleton.elim _ _
  let : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
  let : Nontrivial R := (algebraMap R A).domain_nontrivial
  obtain ⟨n, s, i, hi⟩ := exists_fin_split R M
  let F := Fin n → R
  let : Module.Free A (A ⊗[R] F) :=
    Module.Free.of_basis (Algebra.TensorProduct.basis A (Module.finBasis R F))
  have hiA : (s.baseChange A).comp (i.baseChange A) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hi, LinearMap.baseChange_id]
  rw [det_stabilize s i hi f,
    det_stabilize (s.baseChange A) (i.baseChange A) hiA (f.baseChange A),
    ← LinearMap.det_baseChange]
  congr 1
  simp only [LinearMap.baseChange_add, LinearMap.baseChange_id,
    LinearMap.baseChange_comp, LinearMap.baseChange_sub]

/-- On a finite projective module of constant rank `d`, the scalar determinant of `r • id` is
`r ^ d`. -/
theorem det_smul_id_of_rankAtStalk {R M : Type u}
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    {d : ℕ} (hRank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = d) (r : R) :
    ProjectiveDeterminant.det (r • (LinearMap.id : M →ₗ[R] M)) = r ^ d := by
  classical
  apply Module.eq_of_localization_maximal
    (Mₚ := fun (P : Ideal R) [P.IsMaximal] => Localization.AtPrime P)
    (f := fun (P : Ideal R) [P.IsMaximal] => Algebra.linearMap R (Localization.AtPrime P))
  intro P hP
  let A := Localization.AtPrime P
  let M_A := A ⊗[R] M
  let : Module.Flat A M_A := Module.Flat.of_projective
  let : Module.Free A M_A := Module.free_of_flat_of_isLocalRing
  have hfinrank : Module.finrank A M_A = d := by
    simpa [M_A, hRank ⟨P, hP.isPrime⟩] using
      (Module.rankAtStalk_eq_finrank_tensorProduct (R := R) (M := M)
        (p := ⟨P, hP.isPrime⟩)).symm
  have hdet := ProjectiveDeterminant.det_baseChange_atPrime P
    (r • (LinearMap.id : M →ₗ[R] M))
  have hsmul : ((r • (LinearMap.id : M →ₗ[R] M)).baseChange A) =
      (algebraMap R A r) • (LinearMap.id : M_A →ₗ[A] M_A) := by
    simp only [LinearMap.baseChange_smul, LinearMap.baseChange_id, algebraMap_smul]
  rwa [hsmul, ProjectiveDeterminant.det_eq_linearMap_det_of_basis
      (Module.finBasis A M_A) _, LinearMap.det_smul, LinearMap.det_id, mul_one,
    hfinrank, ← map_pow] at hdet

/-- The scalar determinant is invariant under conjugation by a linear equivalence. -/
theorem det_conj {R M N : Type u}
    [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (e : M ≃ₗ[R] N) (f : M →ₗ[R] M) :
    ProjectiveDeterminant.det (e.toLinearMap.comp (f.comp e.symm.toLinearMap)) =
      ProjectiveDeterminant.det f := by
  classical
  by_cases hR : Subsingleton R
  · let := hR
    exact Subsingleton.elim _ _
  let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
  obtain ⟨n, s, i, hi⟩ := exists_fin_split R M
  let sN := e.toLinearMap.comp s
  let iN := i.comp e.symm.toLinearMap
  have hiN : sN.comp iN = LinearMap.id := by
    ext x
    simp [sN, iN, ← LinearMap.comp_apply, hi]
  rw [det_stabilize sN iN hiN, det_stabilize s i hi]
  congr 1
  ext x
  simp [sN, iN, LinearMap.comp_apply]

/-- The scalar determinant of multiplication by a product. -/
theorem det_lmul_mul {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] (a b : A) :
    ProjectiveDeterminant.det (Algebra.lmul R A (a * b)) =
      ProjectiveDeterminant.det (Algebra.lmul R A a) *
        ProjectiveDeterminant.det (Algebra.lmul R A b) := by
  rw [show Algebra.lmul R A (a * b) =
      (Algebra.lmul R A b).comp (Algebra.lmul R A a) by
    ext x
    change a * b * x = b * (a * x)
    ring]
  simpa [mul_comm] using
    (ProjectiveDeterminant.det_comp (Algebra.lmul R A a) (Algebra.lmul R A b))

/-- The scalar determinant of multiplication by `1`. -/
theorem det_lmul_one {R A : Type u}
    [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Projective R A] :
    ProjectiveDeterminant.det (Algebra.lmul R A 1) = 1 := by
  have hmul : (Algebra.lmul R A 1 : A →ₗ[R] A) = LinearMap.id := by
    ext x
    change (1 : A) * x = x
    simp
  rw [hmul, det_id]

end ProjectiveDeterminant

namespace Algebra

variable (R : Type u) {A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The norm of a commutative algebra `A` which is finite and projective as a module over `R`:
the scalar determinant of multiplication. On a finite free algebra this is `Algebra.norm`. -/
@[sga "3 V 4.1.1"]
noncomputable def projectiveNorm [Module.Finite R A] [Module.Projective R A] : A →* R where
  toFun a := ProjectiveDeterminant.det (Algebra.lmul R A a)
  map_one' := ProjectiveDeterminant.det_lmul_one
  map_mul' := ProjectiveDeterminant.det_lmul_mul

/-- The projective norm of `a` is the scalar determinant of multiplication by `a`. -/
theorem projectiveNorm_apply [Module.Finite R A] [Module.Projective R A] (a : A) :
    projectiveNorm R a = ProjectiveDeterminant.det (Algebra.lmul R A a) := rfl

/-- On a finite free algebra the projective norm is Mathlib's `Algebra.norm`. -/
theorem projectiveNorm_eq_norm_of_free [Module.Finite R A] [Module.Free R A] (a : A) :
    projectiveNorm R a = Algebra.norm R a := by
  classical
  by_cases hR : Subsingleton R
  · let := hR
    exact Subsingleton.elim _ _
  · let : Nontrivial R := not_subsingleton_iff_nontrivial.mp hR
    let b := Module.finBasis R A
    rw [projectiveNorm_apply, ProjectiveDeterminant.det_eq_linearMap_det_of_basis b,
      Algebra.norm_eq_matrix_det b, ← LinearMap.det_toMatrix b,
      ← Algebra.toMatrix_lmul_eq b a]
    have hmul : (Algebra.lmul R A a : A →ₗ[R] A) = LinearMap.mulLeft R a := by
      ext x
      rfl
    rw [hmul]

/-- The projective norm of a scalar is its `d`-th power, when `A` has constant rank `d`
over `R`. -/
theorem projectiveNorm_algebraMap_of_rankAtStalk
    [Module.Finite R A] [Module.Projective R A] {d : ℕ}
    (hRank : ∀ p : PrimeSpectrum R, Module.rankAtStalk A p = d) (r : R) :
    projectiveNorm R (algebraMap R A r) = r ^ d := by
  have hmul : (Algebra.lmul R A (algebraMap R A r) : A →ₗ[R] A) =
      r • (LinearMap.id : A →ₗ[R] A) := by
    ext x
    change algebraMap R A r * x = r • x
    simp [Algebra.smul_def]
  rw [projectiveNorm_apply, hmul]
  exact ProjectiveDeterminant.det_smul_id_of_rankAtStalk hRank r

/-- The projective norm commutes with base change along `R → A`, in tensor-product form. -/
theorem projectiveNorm_baseChange {B : Type u} [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B] (b : B) :
    projectiveNorm A ((1 : A) ⊗ₜ[R] b) = algebraMap R A (projectiveNorm R b) := by
  classical
  let : Module.Finite A (A ⊗[R] B) := inferInstance
  let : Module.Projective A (A ⊗[R] B) := inferInstance
  have hmul :
      (Algebra.lmul A (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b) :
        (A ⊗[R] B) →ₗ[A] (A ⊗[R] B)) =
        (Algebra.lmul R B b).baseChange A := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a x =>
        simp only [LinearMap.baseChange_tmul]
        change ((1 : A) ⊗ₜ[R] b) * (a ⊗ₜ[R] x) = a ⊗ₜ[R] (b * x)
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [projectiveNorm_apply, projectiveNorm_apply, hmul]
  exact (ProjectiveDeterminant.det_baseChange (Algebra.lmul R B b)).symm

/-- The projective norm is invariant under an algebra equivalence. -/
theorem projectiveNorm_algEquiv {B : Type u} [CommRing B] [Algebra R B]
    [Module.Finite R A] [Module.Projective R A]
    [Module.Finite R B] [Module.Projective R B]
    (e : A ≃ₐ[R] B) (a : A) :
    projectiveNorm R (e a) = projectiveNorm R a := by
  have hm : (Algebra.lmul R B (e a) : B →ₗ[R] B) =
      e.toLinearEquiv.toLinearMap.comp
        ((Algebra.lmul R A a).comp e.toLinearEquiv.symm.toLinearMap) := by
    ext b
    change e a * b = e (a * e.symm b)
    rw [map_mul, e.apply_symm_apply]
  rw [projectiveNorm_apply, projectiveNorm_apply, hm]
  exact ProjectiveDeterminant.det_conj e.toLinearEquiv (Algebra.lmul R A a)

/-- The projective norm commutes with base change around an arbitrary pushout square of
commutative rings. -/
theorem projectiveNorm_pushout
    {R A S B : CommRingCat.{u}} (i : R ⟶ A) (j : R ⟶ S)
    (k : A ⟶ B) (l : S ⟶ B) (h : CategoryTheory.IsPushout i j k l) :
    letI := i.hom.toAlgebra
    letI := l.hom.toAlgebra
    ∀ [Module.Finite R A] [Module.Projective R A]
      [Module.Finite S B] [Module.Projective S B] (a : A),
      projectiveNorm S (k a) = j (projectiveNorm R a) := by
  let := i.hom.toAlgebra
  let := j.hom.toAlgebra
  let := l.hom.toAlgebra
  intro _ _ _ _ a
  let e := ((CommRingCat.isPushout_tensorProduct R S A).isoIsPushout S A h.flip)
  let e' : S ⊗[R] A ≃ₐ[S] B := {
    __ := e.commRingCatIsoToRingEquiv
    commutes' s :=
      congr($( (CommRingCat.isPushout_tensorProduct R S A).inl_isoIsPushout_hom
        S A h.flip) s) }
  have hea : e' (1 ⊗ₜ[R] a) = k a :=
    congr($( (CommRingCat.isPushout_tensorProduct R S A).inr_isoIsPushout_hom
      S A h.flip) a)
  rw [← hea, projectiveNorm_algEquiv, projectiveNorm_baseChange]
  rfl

/-- If `a : A` vanishes at a point of `Spec A`, its projective norm vanishes at the image point
of `Spec R`. The point of `Spec A` is given by a ring map `k : A → L` to a field, the image
point by `j : R → K`, and the specialization by the commuting square. -/
theorem projectiveNorm_eq_zero_of_field_hom
    {A K L : Type u} [CommRing A] [Field K] [Field L]
    [Algebra R A] [Module.Finite R A] [Module.Projective R A]
    (j : R →+* K) (k : A →+* L) (l : K →+* L)
    (h : k.comp (algebraMap R A) = l.comp j) (a : A) (ha : k a = 0) :
    j (projectiveNorm R a) = 0 := by
  let := j.toAlgebra
  let := l.toAlgebra
  let : Algebra R L := ((l.comp j).toAlgebra)
  let : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  let k' : A →ₐ[R] L := { __ := k, commutes' r := congr($h r) }
  let μ : K ⊗[R] A →ₐ[K] L :=
    Algebra.TensorProduct.lift (Algebra.ofId K L) k' (fun _ _ => Commute.all _ _)
  have hμ : μ (1 ⊗ₜ[R] a) = 0 := by simp [μ, ha, k']
  change algebraMap R K (projectiveNorm R a) = 0
  rw [← projectiveNorm_baseChange (R := R) (A := K), projectiveNorm_eq_norm_of_free]
  change LinearMap.det (Algebra.lmul K (K ⊗[R] A) (1 ⊗ₜ[R] a)) = 0
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
  intro hker
  have hinj := LinearMap.ker_eq_bot.mp hker
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  exact one_ne_zero <| calc
    1 = μ 1 := (map_one μ).symm
    _ = μ ((1 ⊗ₜ[R] a) * b) := congrArg μ hb.symm
    _ = 0 := by rw [map_mul, hμ, zero_mul]

end Algebra

namespace Module

/-- A module whose localizations at a spanning family are free is flat. -/
private theorem flat_of_free_away {R M ι : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (f : ι → R) (hspan : Ideal.span (Set.range f) = ⊤)
    (h : ∀ i, Module.Free (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) :
    Module.Flat R M :=
  Module.flat_of_localized_span R M (Set.range f) hspan (by
    rintro ⟨r, ⟨i, rfl⟩⟩
    let := h i
    exact Module.Flat.trans R (Localization.Away (f i)) _)

/-- A finite locally free module of constant rank `d` has `rankAtStalk` identically `d`. -/
theorem rankAtStalk_eq_of_isFiniteLocallyFreeOfRank
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (d : ℕ) (h : Module.IsFiniteLocallyFreeOfRank R M d) :
    ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = d := by
  classical
  rcases h with ⟨ι, f, hspan, hbasis⟩
  let S : Set R := Set.range f
  have hS : Ideal.span S = ⊤ := by simpa [S] using hspan
  let : Module.Finite R M :=
    Module.Finite.of_localizationSpan S hS (by
      rintro ⟨r, ⟨i, rfl⟩⟩
      exact Module.Finite.of_basis (hbasis i).some)
  let : Module.Flat R M :=
    flat_of_free_away f hspan fun i => Module.Free.of_basis (hbasis i).some
  intro p
  have hnot : ¬ Set.range f ⊆ (p.asIdeal : Set R) := by
    rw [← Ideal.span_le, hspan, top_le_iff]
    exact p.isPrime.ne_top
  obtain ⟨_, ⟨i, rfl⟩, hap⟩ := Set.not_subset.mp hnot
  let S := Localization.Away (f i)
  let : IsLocalization.Away (f i) S := inferInstance
  have hpRange : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R S)) := by
    rw [PrimeSpectrum.localization_away_comap_range S (f i)]
    exact (PrimeSpectrum.mem_basicOpen (f i) p).2 hap
  obtain ⟨q, hq⟩ := hpRange
  let : Nontrivial S :=
    not_subsingleton_iff_nontrivial.mp fun _ => q.isPrime.ne_top (Subsingleton.elim _ _)
  have hbase := Module.rankAtStalk_isBaseChange
    (LocalizedModule.isBaseChange (Submonoid.powers (f i)) M) q
  let b := (hbasis i).some
  let : Module.Free S (LocalizedModule (Submonoid.powers (f i)) M) :=
    Module.Free.of_basis b
  rw [← hq, ← hbase]
  simpa using Module.finrank_eq_card_basis b

/-- A finite locally free module is finite and projective. -/
theorem finite_and_projective_of_isFiniteLocallyFree
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (h : Module.IsFiniteLocallyFree R M) :
    Module.Finite R M ∧ Module.Projective R M := by
  classical
  rcases h with ⟨ι, f, hspan, hlocal⟩
  let S : Set R := Set.range f
  have hS : Ideal.span S = ⊤ := by simpa [S] using hspan
  let : Module.Finite R M :=
    Module.Finite.of_localizationSpan S hS (by
      rintro ⟨r, ⟨i, rfl⟩⟩
      exact (hlocal i).2)
  let : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan S hS (by
      rintro ⟨r, ⟨i, rfl⟩⟩
      let : Module.Free (Localization.Away (f i))
          (LocalizedModule.Away (f i) M) := (hlocal i).1
      let : Module.Finite (Localization.Away (f i))
          (LocalizedModule.Away (f i) M) := (hlocal i).2
      exact Module.finitePresentation_of_projective _ _)
  let : Module.Flat R M := flat_of_free_away f hspan fun i => (hlocal i).1
  have hp : Module.Projective R M := by
    apply Module.projective_of_localization_maximal
    intro I hI
    let : I.IsPrime := hI.isPrime
    let : IsLocalRing (Localization.AtPrime I) := Localization.AtPrime.isLocalRing I
    let : Module.Finite (Localization.AtPrime I) (LocalizedModule I.primeCompl M) :=
      inferInstance
    let : Module.Flat (Localization.AtPrime I) (LocalizedModule I.primeCompl M) :=
      Module.Flat.of_isLocalizedModule (Localization.AtPrime I) I.primeCompl
        (LocalizedModule.mkLinearMap I.primeCompl M)
    let : Module.Free (Localization.AtPrime I) (LocalizedModule I.primeCompl M) :=
      Module.free_of_flat_of_isLocalRing
    infer_instance
  exact ⟨inferInstance, hp⟩

end Module

end
