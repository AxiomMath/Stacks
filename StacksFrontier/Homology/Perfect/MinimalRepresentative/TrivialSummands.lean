module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative.ElementarySplitting
import all StacksFrontier.Homology.Perfect.MinimalRepresentative.ElementarySplitting

/-!
# Minimal representatives: isomorphism up to trivial summands

Over a local ring, and then after localizing at a prime, two bounded complexes of finite
projective modules with isomorphic images in the derived category become isomorphic once finite
direct sums of trivial two-term complexes are adjoined to both sides. Lifting the comparison maps to
a principal localization `R_f` with `f ∉ p` gives `exists_away_iso_biprod_trivial_complexes`
([stacks 0F9V]).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

open scoped TensorProduct ChangeOfRings

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

set_option backward.isDefEq.respectTransparency false in
private theorem extendScalars_map_eq_zero_of_mem_smul_top
    {R : Type u} [CommRing R] (I : Ideal R) {M N : ModuleCat.{max v u} R}
    (f : M ⟶ N) (hf : ∀ x, f.hom x ∈ I • (⊤ : Submodule R N)) :
    (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    show r ⊗ₜ[R] f.hom x = 0
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    apply (TensorProduct.quotTensorEquivQuotSMul N I).injective
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem _ r (hf x))

private theorem ulift_pi_mem_smul_top
    {R : Type u} [CommRing R] {ι : Type*} [Finite ι]
    (I : Ideal R) (x : ULift.{v} (ι → R)) (hx : ∀ i, x.down i ∈ I) :
    x ∈ I • (⊤ : Submodule R (ULift.{v} (ι → R))) := by
  classical
  let := Fintype.ofFinite ι
  have heq : x = ∑ i, x.down i • (ULift.up (Pi.single i 1) : ULift.{v} (ι → R)) := by
    apply (ULift.moduleEquiv : ULift.{v} (ι → R) ≃ₗ[R] (ι → R)).injective
    simp only [map_sum, map_smul]
    show x.down = ∑ i, x.down i • Pi.single i (1 : R)
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [heq]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (hx i) (Submodule.mem_top))

private theorem freeComplex_reduction_d_eq_zero
    {R : Type u} [CommRing R] (I : Ideal R) (D : FreeComplex R)
    (hD : ∀ i a b, D.d i a b ∈ I) :
    ∀ i j, (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map
      (((liftChainComplexFunctor.{u, v} R).obj D.toComplex).d i j) = 0 := by
  intro i j
  let M := (liftChainComplexFunctor.{u, v} R).obj D.toComplex
  by_cases hij : i + 1 = j
  · apply extendScalars_map_eq_zero_of_mem_smul_top
    intro x
    apply ulift_pi_mem_smul_top
    intro a
    show ((D.toComplex.d (-i) (-j)).hom x.down) a ∈ I
    have hidx : -i = -j + 1 := by omega
    have hd : ∀ k, ∀ h : k = -j + 1, ∀ x : Fin (D.n k) → R,
        ∀ a, ((D.toComplex.d k (-j)).hom x) a ∈ I := by
      rintro k rfl x a
      rw [FreeComplex.toComplex_d_succ]
      show (∑ b, D.d (-j) a b * x b) ∈ I
      exact I.sum_mem fun b _ => I.mul_mem_right _ (hD (-j) a b)
    exact hd (-i) hidx x.down a
  · have hd : M.d i j = 0 := M.shape i j hij
    show (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map (M.d i j) = 0
    rw [hd]
    let := extendScalars_additive.{u, u, max v u} (Ideal.Quotient.mk I)
    exact (ModuleCat.extendScalars (Ideal.Quotient.mk I)).map_zero _ _

private theorem freeComplex_finite_projective_terms
    {R : Type u} [CommRing R] (D : FreeComplex R) :
    ∀ i, Module.Finite R (((liftChainComplexFunctor.{u, v} R).obj D.toComplex).X i) ∧
      Projective (((liftChainComplexFunctor.{u, v} R).obj D.toComplex).X i) := by
  intro i
  show Module.Finite R (ULift.{v} (Fin (D.n (-i)) → R)) ∧
    Projective (ModuleCat.of R (ULift.{v} (Fin (D.n (-i)) → R)))
  exact ⟨inferInstance, ModuleCat.projective_of_free (Module.Free.chooseBasis R _)⟩

private theorem exists_iso_biprod_trivial_complexes_of_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R]
    (M N : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hNbounded : ∃ a b : ℤ, N.IsStrictlyGE a ∧ N.IsStrictlyLE b)
    (hMterms : ∀ i, Module.Finite R (M.X i) ∧ Module.Free R (M.X i))
    (hNterms : ∀ i, Module.Finite R (N.X i) ∧ Module.Free R (N.X i))
    (e : HomotopyEquiv M N) :
    ∃ (m n : ℕ) (degreeM : Fin m → ℤ) (degreeN : Fin n → ℤ),
      Nonempty (M ⊞ (∏ᶜ fun j => CochainComplex.mappingCone
        (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{max v u} R) (degreeN j)).obj
          (ModuleCat.of R (ULift.{v} R))))) ≅
        N ⊞ (∏ᶜ fun j => CochainComplex.mappingCone
          (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{max v u} R) (degreeM j)).obj
            (ModuleCat.of R (ULift.{v} R)))))) := by
  classical
  let U := liftChainComplexFunctor.{u, v} R
  obtain ⟨DM, m, degreeM, _, hDM, ⟨eM⟩⟩ :=
    cochainComplex_exists_iso_biprod_mappingCone_single.{u, v} M
      (fun i => (hMterms i).1) (fun i => (hMterms i).2) hMbounded
  obtain ⟨DN, n, degreeN, _, hDN, ⟨eN⟩⟩ :=
    cochainComplex_exists_iso_biprod_mappingCone_single.{u, v} N
      (fun i => (hNterms i).1) (fun i => (hNterms i).2) hNbounded
  let PM := fun j => CochainComplex.mappingCone
    (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{max v u} R) (degreeM j)).obj
      (ModuleCat.of R (ULift.{v} R))))
  let PN := fun j => CochainComplex.mappingCone
    (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{max v u} R) (degreeN j)).obj
      (ModuleCat.of R (ULift.{v} R))))
  obtain ⟨hPM⟩ := homotopy_id_zero_product m PM
    (fun j => ⟨CochainComplex.mappingCone.homotopyToZeroOfId _⟩)
  obtain ⟨hPN⟩ := homotopy_id_zero_product n PN
    (fun j => ⟨CochainComplex.mappingCone.homotopyToZeroOfId _⟩)
  obtain ⟨hM⟩ := homotopyEquiv_biprod_of_contractible (U.obj DM.toComplex) (∏ᶜ PM) hPM
  obtain ⟨hN⟩ := homotopyEquiv_biprod_of_contractible (U.obj DN.toComplex) (∏ᶜ PN) hPN
  let h : HomotopyEquiv (U.obj DM.toComplex) (U.obj DN.toComplex) :=
    ((HomotopyEquiv.ofIso eM).trans hM).symm.trans
      (e.trans ((HomotopyEquiv.ofIso eN).trans hN))
  have hI : ∀ x : R, x ∈ IsLocalRing.maximalIdeal R → IsUnit (1 + x) := by
    intro x hx
    rw [← IsLocalRing.notMem_maximalIdeal]
    intro hx'
    have hone : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      simpa using (IsLocalRing.maximalIdeal R).sub_mem hx' hx
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 hone)
  let : IsIso h.hom :=
    isIso_homotopyEquiv_hom_of_zero_differentials_reduction
      (IsLocalRing.maximalIdeal R) hI
      (freeComplex_finite_projective_terms.{u, v} DM)
      (freeComplex_finite_projective_terms.{u, v} DN) h
      (freeComplex_reduction_d_eq_zero.{u, v} _ DM hDM)
      (freeComplex_reduction_d_eq_zero.{u, v} _ DN hDN)
  exact ⟨m, n, degreeM, degreeN, exists_iso_biprod_of_iso_biprod eM eN (asIso h.hom)⟩

private theorem exists_iso_biprod_trivial_complexes_atPrime
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (M N : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hNbounded : ∃ a b : ℤ, N.IsStrictlyGE a ∧ N.IsStrictlyLE b)
    (hMterms : ∀ i, Module.Finite R (M.X i) ∧ Projective (M.X i))
    (hNterms : ∀ i, Module.Finite R (N.X i) ∧ Projective (N.X i))
    (hMN : Nonempty (DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj N)) :
    let S := Localization.AtPrime p
    let F := (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.up ℤ)
    ∃ (m n : ℕ) (degreeM : Fin m → ℤ) (degreeN : Fin n → ℤ),
      Nonempty (F.obj M ⊞ (∏ᶜ fun j => CochainComplex.mappingCone
        (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{max v u} S) (degreeN j)).obj
          (ModuleCat.of S (ULift.{v} S))))) ≅
        F.obj N ⊞ (∏ᶜ fun j => CochainComplex.mappingCone
          (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{max v u} S) (degreeM j)).obj
            (ModuleCat.of S (ULift.{v} S)))))) := by
  obtain ⟨e⟩ := homotopyEquiv_atPrime_of_derivedIso.{u, v} p M N hMbounded hNbounded
    hMterms hNterms hMN.some
  exact exists_iso_biprod_trivial_complexes_of_isLocalRing.{u, v} _ _
    (bounded_extendScalars.{u, v} _ M hMbounded)
    (bounded_extendScalars.{u, v} _ N hNbounded)
    (fun i => ⟨finite_extendScalars.{u, v} _ _ (hMterms i).1,
      free_extendScalars_atPrime.{u, v} p _ (hMterms i).1 (hMterms i).2⟩)
    (fun i => ⟨finite_extendScalars.{u, v} _ _ (hNterms i).1,
      free_extendScalars_atPrime.{u, v} p _ (hNterms i).1 (hNterms i).2⟩) e

private theorem mapExtendScalars_tensorProduct_eq_baseChange
    {R : Type*} [CommRing R] (T : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization T S]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) :
    IsLocalizedModule.mapExtendScalars T (TensorProduct.mk R S M 1)
      (TensorProduct.mk R S N 1) S f = f.baseChange S := by
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext T (TensorProduct.mk R S M 1)
    (TensorProduct.mk R S N 1)
  ext x
  show IsLocalizedModule.map T (TensorProduct.mk R S M 1)
    (TensorProduct.mk R S N 1) f (1 ⊗ₜ[R] x) = 1 ⊗ₜ[R] f x
  exact IsLocalizedModule.map_apply _ _ _ _ _

/-- Finitely many localization maps can be cleared by one common denominator. -/
private theorem exists_smul_eq_map_pi
    {R : Type*} [CommRing R] (T : Submonoid R) {ι : Type*} [Finite ι] {A B : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module R (A i)]
    [∀ i, Module R (B i)] (L : ∀ i, A i →ₗ[R] B i) [∀ i, IsLocalizedModule T (L i)]
    (y : ∀ i, B i) : ∃ (x : ∀ i, A i) (t : T), ∀ i, L i (x i) = (t : R) • y i := by
  let : IsLocalizedModule T (LinearMap.pi fun i => (L i).comp (LinearMap.proj i)) :=
    IsLocalizedModule.pi T L
  obtain ⟨⟨x, t⟩, h⟩ := IsLocalizedModule.surj T (LinearMap.pi fun i => (L i).comp
    (LinearMap.proj i)) y
  exact ⟨x, t, fun i => (congrFun h i).symm⟩

/-- Finitely many elements killed by localization maps are killed by one common element. -/
private theorem exists_smul_eq_zero_of_map_pi_eq_zero
    {R : Type*} [CommRing R] (T : Submonoid R) {ι : Type*} [Finite ι] {A B : ι → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, Module R (A i)]
    [∀ i, Module R (B i)] (L : ∀ i, A i →ₗ[R] B i) [∀ i, IsLocalizedModule T (L i)]
    (x : ∀ i, A i) (hx : ∀ i, L i (x i) = 0) : ∃ t : T, ∀ i, (t : R) • x i = 0 := by
  let : IsLocalizedModule T (LinearMap.pi fun i => (L i).comp (LinearMap.proj i)) :=
    IsLocalizedModule.pi T L
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff T (LinearMap.pi fun i => (L i).comp
    (LinearMap.proj i))).mp (funext hx)
  exact ⟨t, fun i => congrFun ht i⟩

private theorem exists_baseChange_eq_smul
    {R : Type*} [CommRing R] (T : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization T S]
    {ι : Type*} [Finite ι] {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (M i)] [∀ i, Module R (N i)]
    [∀ i, Module.FinitePresentation R (M i)]
    (f : ∀ i, S ⊗[R] M i →ₗ[S] S ⊗[R] N i) :
    ∃ (g : ∀ i, M i →ₗ[R] N i) (t : T), ∀ i, (g i).baseChange S = (t : R) • f i := by
  obtain ⟨g, t, h⟩ := exists_smul_eq_map_pi T (fun i => IsLocalizedModule.mapExtendScalars T
    (TensorProduct.mk R S (M i) 1) (TensorProduct.mk R S (N i) 1) S) f
  exact ⟨g, t, fun i => by rw [← mapExtendScalars_tensorProduct_eq_baseChange T S]; exact h i⟩

private theorem exists_smul_eq_zero_of_baseChange_eq_zero
    {R : Type*} [CommRing R] (T : Submonoid R) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization T S]
    {ι : Type*} [Finite ι] {M N : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (M i)] [∀ i, Module R (N i)]
    [∀ i, Module.FinitePresentation R (M i)]
    (f : ∀ i, M i →ₗ[R] N i) (hf : ∀ i, (f i).baseChange S = 0) :
    ∃ t : T, ∀ i, (t : R) • f i = 0 := by
  refine exists_smul_eq_zero_of_map_pi_eq_zero T (fun i => IsLocalizedModule.mapExtendScalars T
    (TensorProduct.mk R S (M i) 1) (TensorProduct.mk R S (N i) 1) S) f fun i => ?_
  rw [mapExtendScalars_tensorProduct_eq_baseChange, hf]

private theorem exists_lift_complex_map
    {R : Type u} [CommRing R] (T : Submonoid R)
    (M N : CochainComplex (ModuleCat.{v} R) ℤ)
    (M' N' : ℤ → Type*) [∀ i, AddCommGroup (M' i)] [∀ i, AddCommGroup (N' i)]
    [∀ i, Module R (M' i)] [∀ i, Module R (N' i)]
    (μ : ∀ i, M.X i →ₗ[R] M' i) (ν : ∀ i, N.X i →ₗ[R] N' i)
    [∀ i, IsLocalizedModule T (μ i)] [∀ i, IsLocalizedModule T (ν i)]
    (hM : ∀ i, Module.FinitePresentation R (M.X i))
    (s : Finset ℤ) (hs : ∀ i, i ∉ s → IsZero (M.X i))
    (e : ∀ i, M' i →ₗ[R] N' i)
    (he : ∀ i, (IsLocalizedModule.map T (ν i) (ν (i + 1)) (N.d i (i + 1)).hom).comp (e i) =
      (e (i + 1)).comp (IsLocalizedModule.map T (μ i) (μ (i + 1)) (M.d i (i + 1)).hom)) :
    ∃ (g : M ⟶ N) (t : T), ∀ i,
      IsLocalizedModule.map T (μ i) (ν i) (g.f i).hom = (t : R) • e i := by
  classical
  let := hM
  let L (i : ℤ) := IsLocalizedModule.map T (μ i) (ν i)
  let : ∀ i : s, IsLocalizedModule T (L i.val) := fun _ => inferInstance
  obtain ⟨g, t, hg⟩ := exists_smul_eq_map_pi T (fun i : s => L i.val) (fun i : s => e i.val)
  let g₀ (i : ℤ) : M.X i →ₗ[R] N.X i := if hi : i ∈ s then g ⟨i, hi⟩ else 0
  have hg₀ (i : ℤ) : L i (g₀ i) = (t : R) • e i := by
    by_cases hi : i ∈ s
    · simpa only [Submonoid.smul_def, g₀, dite_eq_left hi] using hg ⟨i, hi⟩
    · have hsub : Subsingleton (M.X i) := ModuleCat.subsingleton_of_isZero (hs i hi)
      have : Subsingleton (M' i) :=
        IsLocalizedModule.subsingleton_of_subsingleton T (μ i)
      have hez : e i = 0 := Subsingleton.elim _ _
      simp [g₀, hi, hez]
  let δ (i : ℤ) := (N.d i (i + 1)).hom.comp (g₀ i) -
    (g₀ (i + 1)).comp (M.d i (i + 1)).hom
  let D (i : s) := IsLocalizedModule.map T (μ i.val) (ν (i.val + 1))
  let : ∀ i : s, IsLocalizedModule T (D i) := fun _ => inferInstance
  obtain ⟨q, hq⟩ := exists_smul_eq_zero_of_map_pi_eq_zero T D (fun i : s => δ i.val) fun i => by
    dsimp only [D, δ]
    rw [map_sub, IsLocalizedModule.map_comp' T (μ i.val) (ν i.val) (ν (i.val + 1)),
      IsLocalizedModule.map_comp' T (μ i.val) (μ (i.val + 1)) (ν (i.val + 1))]
    show _ - _ = 0
    rw [show IsLocalizedModule.map T (μ i.val) (ν i.val) (g₀ i.val) = _ from hg₀ i.val,
      show IsLocalizedModule.map T (μ (i.val + 1)) (ν (i.val + 1)) (g₀ (i.val + 1)) = _ from
        hg₀ (i.val + 1),
      LinearMap.comp_smul, LinearMap.smul_comp, he, sub_self]
  let g' : M ⟶ N := {
    f i := ModuleCat.ofHom ((q : R) • g₀ i)
    comm' i j hij := by
      have hj : i + 1 = j := hij
      subst j
      by_cases hi : i ∈ s
      · apply ModuleCat.hom_ext
        show (N.d i (i + 1)).hom.comp ((q : R) • g₀ i) =
          ((q : R) • g₀ (i + 1)).comp (M.d i (i + 1)).hom
        rw [LinearMap.comp_smul, LinearMap.smul_comp, ← sub_eq_zero, ← smul_sub]
        exact hq ⟨i, hi⟩
      · exact (hs i hi).eq_of_src _ _ }
  refine ⟨g', q * t, fun i => ?_⟩
  show L i ((q : R) • g₀ i) = ((q * t : T) : R) • e i
  rw [map_smul, hg₀, Submonoid.coe_mul, mul_smul]

private theorem exists_away_bijective_components
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (M N : CochainComplex (ModuleCat.{v} R) ℤ)
    (M' N' : ℤ → Type*) [∀ i, AddCommGroup (M' i)] [∀ i, AddCommGroup (N' i)]
    [∀ i, Module R (M' i)] [∀ i, Module R (N' i)]
    (μ : ∀ i, M.X i →ₗ[R] M' i) (ν : ∀ i, N.X i →ₗ[R] N' i)
    [∀ i, IsLocalizedModule p.primeCompl (μ i)] [∀ i, IsLocalizedModule p.primeCompl (ν i)]
    (hM : ∀ i, Module.Finite R (M.X i))
    (hN : ∀ i, Module.FinitePresentation R (N.X i))
    (s : Finset ℤ) (hsM : ∀ i, i ∉ s → IsZero (M.X i))
    (hsN : ∀ i, i ∉ s → IsZero (N.X i))
    (g : M ⟶ N)
    (hg : ∀ i, Function.Bijective (IsLocalizedModule.map p.primeCompl (μ i) (ν i) (g.f i).hom)) :
    ∃ f : R, f ∉ p ∧
      ∀ i, Function.Bijective (LocalizedModule.map (Submonoid.powers f) (g.f i).hom) := by
  classical
  let := hM
  let := hN
  have h (i : s) := exists_bijective_map_powers p.primeCompl (μ i.val) (ν i.val)
    (g.f i.val).hom (hg i.val)
  choose f hf hgood using h
  refine ⟨∏ i : s, f i, ?_, fun i => ?_⟩
  · exact p.primeCompl.prod_mem fun i _ => hf i
  · by_cases hi : i ∈ s
    · exact hgood ⟨i, hi⟩ _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨i, hi⟩ : s)))
    · let := ModuleCat.subsingleton_of_isZero (hsM i hi)
      let := ModuleCat.subsingleton_of_isZero (hsN i hi)
      constructor
      · intro x y _
        exact Subsingleton.elim x y
      · intro y
        exact ⟨0, Subsingleton.elim _ _⟩

set_option backward.isDefEq.respectTransparency false in
private theorem exists_iso_away_of_localized_equiv
    {R : Type u} [CommRing R] [Small.{v} R] (p : Ideal R) [p.IsPrime]
    (M N : CochainComplex (ModuleCat.{v} R) ℤ)
    (M' N' : ℤ → Type*) [∀ i, AddCommGroup (M' i)] [∀ i, AddCommGroup (N' i)]
    [∀ i, Module R (M' i)] [∀ i, Module R (N' i)]
    (μ : ∀ i, M.X i →ₗ[R] M' i) (ν : ∀ i, N.X i →ₗ[R] N' i)
    [∀ i, IsLocalizedModule p.primeCompl (μ i)] [∀ i, IsLocalizedModule p.primeCompl (ν i)]
    (hM : ∀ i, Module.FinitePresentation R (M.X i))
    (hN : ∀ i, Module.FinitePresentation R (N.X i))
    (s : Finset ℤ) (hsM : ∀ i, i ∉ s → IsZero (M.X i))
    (hsN : ∀ i, i ∉ s → IsZero (N.X i))
    (e : ∀ i, M' i ≃ₗ[R] N' i)
    (he : ∀ i, (IsLocalizedModule.map p.primeCompl (ν i) (ν (i + 1)) (N.d i (i + 1)).hom).comp
        (e i).toLinearMap =
      (e (i + 1)).toLinearMap.comp
        (IsLocalizedModule.map p.primeCompl (μ i) (μ (i + 1)) (M.d i (i + 1)).hom)) :
    ∃ f : R, f ∉ p ∧
      let F := (ModuleCat.localizedModuleFunctor.{v} (Submonoid.powers f)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      Nonempty (F.obj M ≅ F.obj N) := by
  obtain ⟨g, t, hg⟩ := exists_lift_complex_map p.primeCompl M N M' N' μ ν hM s hsM
    (fun i => (e i).toLinearMap) he
  have hbij (i : ℤ) : Function.Bijective
      (IsLocalizedModule.map p.primeCompl (μ i) (ν i) (g.f i).hom) := by
    rw [hg]
    exact ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (ν i) t)).comp (e i).bijective
  let := hM
  obtain ⟨f, hf, hfg⟩ := exists_away_bijective_components p M N M' N' μ ν
    (fun i => inferInstance) hN s hsM hsN g hbij
  refine ⟨f, hf, ?_⟩
  let F := (ModuleCat.localizedModuleFunctor.{v} (Submonoid.powers f)).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have (i : ℤ) : IsIso ((F.map g).f i) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
      ((M.X i).localizedModuleMkLinearMap (Submonoid.powers f))
      ((N.X i).localizedModuleMkLinearMap (Submonoid.powers f))).mpr (hfg i)
  have : IsIso (F.map g) := HomologicalComplex.Hom.isIso_of_components _
  exact ⟨asIso (F.map g)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem extendScalarsTensorIso_hom_tmul
    {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (M : ModuleCat.{max v u} R) (s : S) (m : M) :
    (PseudoCoherence.extendScalarsTensorIso (S := S) M).hom (s ⊗ₜ[R, algebraMap R S] m) =
      s ⊗ₜ[R] m := by
  -- `PseudoCoherence.extendScalarsTensorIso` is the identity transported along
  -- `(algebraMap R S).toAlgebra = ‹Algebra R S›`; rewriting the instance back makes the
  -- transport reflexivity.
  rw [← toAlgebra_algebraMap (R := R) (S := S)]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exists_extendScalars_iso_localizedModuleFunctor
    {R : Type u} [CommRing R] (T : Submonoid R) :
    Nonempty (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization T)) ≅
      ModuleCat.localizedModuleFunctor.{max v u} T) := by
  let S := Localization T
  let E (M : ModuleCat.{max v u} R) :=
    (IsLocalizedModule.isBaseChange T S (M.localizedModuleMkLinearMap T)).equiv
  refine ⟨NatIso.ofComponents
    (fun M => PseudoCoherence.extendScalarsTensorIso (S := S) M ≪≫ (E M).toModuleIso) ?_⟩
  intro M N f
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  show E N ((PseudoCoherence.extendScalarsTensorIso (S := S) N).hom
    (((ModuleCat.extendScalars (algebraMap R S)).map f).hom
      ((1 : S) ⊗ₜ[R, algebraMap R S] m))) =
    ((ModuleCat.localizedModuleFunctor T).map f).hom
      (E M ((PseudoCoherence.extendScalarsTensorIso (S := S) M).hom
        ((1 : S) ⊗ₜ[R, algebraMap R S] m)))
  rw [ModuleCat.ExtendScalars.map_tmul, extendScalarsTensorIso_hom_tmul,
    extendScalarsTensorIso_hom_tmul]
  simp only [E, IsBaseChange.equiv_tmul, one_smul]
  exact (IsLocalizedModule.map_apply T (M.localizedModuleMkLinearMap T)
    (N.localizedModuleMkLinearMap T) f.hom m).symm

/-- The mapping cone of the identity of `X` placed in degree `b`, with `X` in degrees
`b - 1` and `b`. -/
private noncomputable abbrev trivialCone {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasBinaryBiproducts C] (b : ℤ) (X : C) : CochainComplex C ℤ :=
  CochainComplex.mappingCone (𝟙 ((CochainComplex.singleFunctor C b).obj X))

private noncomputable def trivialConeXIso {C : Type*} [Category C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C] (X : C) (a b : ℤ) (hab : a + 1 = b) :
    (trivialCone b X).X a ≅ X :=
  let S := (CochainComplex.singleFunctor C b).obj X
  have hzero : IsZero (S.X a) := HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have : IsIso (biprod.inl : S.X b ⟶ S.X b ⊞ S.X a) :=
    (CategoryTheory.Biprod.isIso_inl_iff_isZero _ _).mpr hzero
  HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 S) a b hab ≪≫
    (asIso (biprod.inl : S.X b ⟶ _)).symm ≪≫ HomologicalComplex.singleObjXSelf _ _ _

set_option backward.isDefEq.respectTransparency false in
private theorem exists_iso_trivialCone_of_contractible
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
    (K : CochainComplex C ℤ) (X : C) (a b : ℤ) (hab : a + 1 = b)
    (hK : ∀ k, k ≠ a → k ≠ b → IsZero (K.X k)) (h : Homotopy (𝟙 K) 0)
    (e : K.X a ≅ X) : Nonempty (K ≅ trivialCone b X) := by
  let S := (CochainComplex.singleFunctor C b).obj X
  have hN := mappingCone_single_isZero_X X a b hab
  let : IsIso (K.d a b) := cochainComplex_isIso_d_of_contractible_two_term K a b hab hK h
  let : IsIso ((trivialCone b X).d a b) :=
    cochainComplex_isIso_d_of_contractible_two_term _ a b hab hN
      (CochainComplex.mappingCone.homotopyToZeroOfId S)
  exact cochainComplex_iso_of_two_term K _ a b hab hK hN
    (e ≪≫ (trivialConeXIso X a b hab).symm)

private noncomputable def extendScalarsULiftIso {R : Type u} [CommRing R]
    (S : Type u) [CommRing S] [Algebra R S] :
    (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R S)).obj
      (ModuleCat.of R (ULift.{v} R)) ≅ ModuleCat.of S (ULift.{v} S) :=
  PseudoCoherence.extendScalarsTensorIso (S := S) _ ≪≫ LinearEquiv.toModuleIso
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S) ULift.moduleEquiv).trans
      ((TensorProduct.AlgebraTensorModule.rid R S S).trans ULift.moduleEquiv.symm))

set_option backward.isDefEq.respectTransparency false in
private theorem exists_extendScalars_trivialCone_iso
    {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S] (d : ℤ) :
    let F := (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.up ℤ)
    Nonempty (F.obj (trivialCone d (ModuleCat.of R (ULift.{v} R))) ≅
      trivialCone d (ModuleCat.of S (ULift.{v} S))) := by
  intro F
  let G := ModuleCat.extendScalars.{u, u, max v u} (algebraMap R S)
  let := extendScalars_additive.{u, u, max v u} (algebraMap R S)
  let T := (CochainComplex.singleFunctor (ModuleCat.{max v u} R) d).obj
    (ModuleCat.of R (ULift.{v} R))
  have hK := mappingCone_single_isZero_X (ModuleCat.of R (ULift.{v} R)) (d - 1) d (by omega)
  have hFK : ∀ k, k ≠ d - 1 → k ≠ d →
      IsZero ((F.obj (trivialCone d (ModuleCat.of R (ULift.{v} R)))).X k) :=
    fun k h₀ h₁ => G.map_isZero (hK k h₀ h₁)
  have h : Homotopy (𝟙 (F.obj (trivialCone d (ModuleCat.of R (ULift.{v} R))))) 0 := by
    simpa using G.mapHomotopy (CochainComplex.mappingCone.homotopyToZeroOfId T)
  exact exists_iso_trivialCone_of_contractible _ _ (d - 1) d (by omega) hFK h
    (G.mapIso (trivialConeXIso _ (d - 1) d (by omega)) ≪≫ extendScalarsULiftIso.{u, v} S)

private theorem exists_extendScalars_biprod_trivialCones_iso
    {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    (M : CochainComplex (ModuleCat.{max v u} R) ℤ) {n : ℕ} (degree : Fin n → ℤ) :
    let F := (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.up ℤ)
    Nonempty (F.obj (M ⊞ ∏ᶜ fun j => trivialCone (C := ModuleCat.{max v u} R) (degree j)
        (ModuleCat.of R (ULift.{v} R))) ≅
      F.obj M ⊞ ∏ᶜ fun j => CochainComplex.mappingCone
        (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{max v u} S) (degree j)).obj
          (ModuleCat.of S (ULift.{v} S))))) := by
  intro F
  let := extendScalars_additive.{u, u, max v u} (algebraMap R S)
  let : PreservesFiniteBiproducts F := inferInstance
  let : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  let : PreservesFiniteProducts F := inferInstance
  let e₁ := PreservesProduct.iso F fun j => trivialCone (C := ModuleCat.{max v u} R) (degree j)
    (ModuleCat.of R (ULift.{v} R))
  let e₂ : (∏ᶜ fun j => F.obj (trivialCone (C := ModuleCat.{max v u} R) (degree j)
      (ModuleCat.of R (ULift.{v} R)))) ≅ ∏ᶜ fun j => CochainComplex.mappingCone
        (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{max v u} S) (degree j)).obj
          (ModuleCat.of S (ULift.{v} S)))) :=
    let et j := (exists_extendScalars_trivialCone_iso.{u, v} S (degree j)).some
    { hom := Pi.lift fun j => Pi.π _ j ≫ (et j).hom
      inv := Pi.lift fun j => Pi.π _ j ≫ (et j).inv
      hom_inv_id := Pi.hom_ext _ _ fun j => by simp
      inv_hom_id := Pi.hom_ext _ _ fun j => by simp }
  exact ⟨F.mapBiprod _ _ ≪≫ biprod.mapIso (Iso.refl _) (e₁ ≪≫ e₂)⟩

private theorem isZero_pi_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C] {J : Type*}
    (f : J → C) [HasProduct f] (h : ∀ j, IsZero (f j)) : IsZero (∏ᶜ f) := by
  rw [IsZero.iff_id_eq_zero]
  exact Pi.hom_ext _ _ fun j => (h j).eq_of_tgt _ _

private theorem finite_projective_of_iso {R : Type u} [CommRing R]
    {X Y : ModuleCat.{max v u} R} (e : X ≅ Y) (h : Module.Finite R X ∧ Projective X) :
    Module.Finite R Y ∧ Projective Y := by
  let := h.1
  exact ⟨Module.Finite.equiv e.toLinearEquiv, Projective.of_iso e h.2⟩

private theorem finite_projective_of_isZero {R : Type u} [CommRing R]
    {X : ModuleCat.{max v u} R} (h : IsZero X) : Module.Finite R X ∧ Projective X := by
  let := ModuleCat.subsingleton_of_isZero h
  exact ⟨inferInstance, h.projective⟩

private theorem finite_projective_biprod {R : Type u} [CommRing R]
    {X Y : ModuleCat.{max v u} R} (hX : Module.Finite R X ∧ Projective X)
    (hY : Module.Finite R Y ∧ Projective Y) :
    Module.Finite R (X ⊞ Y : ModuleCat.{max v u} R) ∧ Projective (X ⊞ Y) := by
  let := hX.1
  let := hY.1
  let := hX.2
  let := hY.2
  exact ⟨Module.Finite.equiv (ModuleCat.biprodIsoProd X Y).symm.toLinearEquiv, inferInstance⟩

private theorem finite_projective_pi {R : Type u} [CommRing R] {n : ℕ}
    (X : Fin n → ModuleCat.{max v u} R) (hX : ∀ j, Module.Finite R (X j) ∧ Projective (X j)) :
    Module.Finite R (∏ᶜ X : ModuleCat.{max v u} R) ∧ Projective (∏ᶜ X) := by
  induction n with
  | zero => exact finite_projective_of_isZero (isZero_pi_of_isZero _ fun j => j.elim0)
  | succ n ih =>
    have e := (exists_iso_biprod_product_fin_cons (X 0) (Fin.tail X)).some
    rw [Fin.cons_self_tail] at e
    exact finite_projective_of_iso e
      (finite_projective_biprod (hX 0) (ih _ fun j => hX j.succ))

private theorem trivialCone_finite_projective {R : Type u} [CommRing R] (d i : ℤ) :
    Module.Finite R ((trivialCone d (ModuleCat.of R (ULift.{v} R))).X i) ∧
      Projective ((trivialCone d (ModuleCat.of R (ULift.{v} R))).X i) := by
  classical
  let T := (CochainComplex.singleFunctor (ModuleCat.{max v u} R) d).obj
    (ModuleCat.of R (ULift.{v} R))
  have hT (k : ℤ) : Module.Finite R (T.X k) ∧ Projective (T.X k) := by
    by_cases hk : k = d
    · refine finite_projective_of_iso
        (HomologicalComplex.singleObjXIsoOfEq _ d (ModuleCat.of R (ULift.{v} R)) k hk).symm ?_
      exact ⟨inferInstance, ModuleCat.projective_of_free (Module.Free.chooseBasis R _)⟩
    · exact finite_projective_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hk)
  exact finite_projective_of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod (𝟙 T) i (i + 1) rfl).symm
    (finite_projective_biprod (hT _) (hT _))

private theorem biprod_trivialCones_finite_projective {R : Type u} [CommRing R]
    (M : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hM : ∀ i, Module.Finite R (M.X i) ∧ Projective (M.X i)) {n : ℕ} (degree : Fin n → ℤ)
    (i : ℤ) :
    Module.Finite R ((M ⊞ ∏ᶜ fun j => trivialCone (degree j)
        (ModuleCat.of R (ULift.{v} R))).X i) ∧
      Projective ((M ⊞ ∏ᶜ fun j => trivialCone (degree j)
        (ModuleCat.of R (ULift.{v} R))).X i) := by
  refine finite_projective_of_iso (HomologicalComplex.biprodXIso _ _ i).symm
    (finite_projective_biprod (hM i) ?_)
  exact finite_projective_of_iso
    (PreservesProduct.iso (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) _).symm
    (finite_projective_pi _ fun j => trivialCone_finite_projective.{u, v} (degree j) i)

private theorem exists_finset_isZero_biprod_trivialCones {R : Type u} [CommRing R]
    (M : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b) {n : ℕ}
    (degree : Fin n → ℤ) :
    ∃ s : Finset ℤ, ∀ i, i ∉ s → IsZero ((M ⊞ ∏ᶜ fun j => trivialCone (degree j)
        (ModuleCat.of R (ULift.{v} R))).X i) := by
  classical
  obtain ⟨a, b, ha, hb⟩ := hbounded
  refine ⟨Finset.Icc a b ∪ Finset.univ.image degree ∪
    Finset.univ.image (fun j => degree j - 1), fun i hi => ?_⟩
  simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_image, Finset.mem_univ, true_and,
    not_or, not_and_or, not_le, not_exists] at hi
  obtain ⟨⟨hab, hd⟩, hd'⟩ := hi
  refine IsZero.of_iso ?_ (HomologicalComplex.biprodXIso _ _ i)
  rw [biprod_isZero_iff]
  refine ⟨?_, ?_⟩
  · rcases hab with h | h
    · exact M.isZero_of_isStrictlyGE a i h
    · exact M.isZero_of_isStrictlyLE b i h
  · refine IsZero.of_iso ?_
      (PreservesProduct.iso (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) _)
    exact isZero_pi_of_isZero _ fun j => mappingCone_single_isZero_X _ (degree j - 1)
      (degree j) (by omega) i (fun h => hd' j h.symm) (fun h => hd j h.symm)

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0F9V.** Two bounded complexes of finite projective modules representing
isomorphic derived objects become isomorphic as complexes over some principal localization,
after adjoining finite direct sums of trivial two-term complexes on both sides. -/
@[stacks 0F9V]
theorem exists_away_iso_biprod_trivial_complexes
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
    (M N : CochainComplex (ModuleCat.{max v u} R) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hNbounded : ∃ a b : ℤ, N.IsStrictlyGE a ∧ N.IsStrictlyLE b)
    (hMterms : ∀ i, Module.Finite R (M.X i) ∧ Projective (M.X i))
    (hNterms : ∀ i, Module.Finite R (N.X i) ∧ Projective (N.X i))
    (hMN : Nonempty ((DerivedCategory.Q).obj M ≅ (DerivedCategory.Q).obj N)) :
    ∃ f : R, f ∉ p ∧
      let S := Localization.Away f
      let F := (ModuleCat.extendScalars.{u, u, max v u} (algebraMap R S)).mapHomologicalComplex
        (ComplexShape.up ℤ)
      let IsTrivialSum := fun P : CochainComplex (ModuleCat.{max v u} S) ℤ =>
        ∃ (n : ℕ) (degree : Fin n → ℤ),
          Nonempty (P ≅ ∏ᶜ fun j => CochainComplex.mappingCone
            (𝟙 ((CochainComplex.singleFunctor (ModuleCat.{max v u} S) (degree j)).obj
              (ModuleCat.of S (ULift.{v} S)))))
      ∃ P Q : CochainComplex (ModuleCat.{max v u} S) ℤ,
        IsTrivialSum P ∧ IsTrivialSum Q ∧ Nonempty (F.obj M ⊞ P ≅ F.obj N ⊞ Q) := by
  classical
  obtain ⟨m, n, degreeM, degreeN, ⟨E⟩⟩ :=
    exists_iso_biprod_trivial_complexes_atPrime.{u, v} p M N hMbounded hNbounded
      hMterms hNterms hMN
  let M₁ := M ⊞ ∏ᶜ fun j => trivialCone (degreeN j) (ModuleCat.of R (ULift.{v} R))
  let N₁ := N ⊞ ∏ᶜ fun j => trivialCone (degreeM j) (ModuleCat.of R (ULift.{v} R))
  let Sp := Localization.AtPrime p
  let := extendScalars_additive.{u, u, max v u} (algebraMap R Sp)
  let E₁ := (exists_extendScalars_biprod_trivialCones_iso.{u, v} Sp M degreeN).some ≪≫ E ≪≫
    (exists_extendScalars_biprod_trivialCones_iso.{u, v} Sp N degreeM).some.symm
  let ηp := (exists_extendScalars_iso_localizedModuleFunctor.{u, v} p.primeCompl).some
  let E₂ := ((NatIso.mapHomologicalComplex ηp (ComplexShape.up ℤ)).app M₁).symm ≪≫ E₁ ≪≫
    (NatIso.mapHomologicalComplex ηp (ComplexShape.up ℤ)).app N₁
  have hM₁ := biprod_trivialCones_finite_projective.{u, v} M hMterms degreeN
  have hN₁ := biprod_trivialCones_finite_projective.{u, v} N hNterms degreeM
  have hfp (X : ModuleCat.{max v u} R) (h : Module.Finite R X ∧ Projective X) :
      Module.FinitePresentation R X := by
    let := h.1
    let := h.2
    let := ModuleCat.projective_of_module_projective X
    exact Module.finitePresentation_of_projective R X
  obtain ⟨s₁, hs₁⟩ := exists_finset_isZero_biprod_trivialCones.{u, v} M hMbounded degreeN
  obtain ⟨s₂, hs₂⟩ := exists_finset_isZero_biprod_trivialCones.{u, v} N hNbounded degreeM
  obtain ⟨f, hf, ⟨E₃⟩⟩ := exists_iso_away_of_localized_equiv.{u, max v u} p M₁ N₁
    (fun i => (M₁.X i).localizedModule p.primeCompl)
    (fun i => (N₁.X i).localizedModule p.primeCompl)
    (fun i => (M₁.X i).localizedModuleMkLinearMap p.primeCompl)
    (fun i => (N₁.X i).localizedModuleMkLinearMap p.primeCompl)
    (fun i => hfp _ (hM₁ i)) (fun i => hfp _ (hN₁ i)) (s₁ ∪ s₂)
    (fun i hi => hs₁ i (fun h => hi (Finset.mem_union_left _ h)))
    (fun i hi => hs₂ i (fun h => hi (Finset.mem_union_right _ h)))
    (fun i => (Iso.toLinearEquiv (X := (M₁.X i).localizedModule p.primeCompl)
      (Y := (N₁.X i).localizedModule p.primeCompl)
      ((HomologicalComplex.eval _ _ i).mapIso E₂)).restrictScalars R)
    (by
      intro i
      apply LinearMap.ext
      intro x
      have h := congr(($(E₂.hom.comm i (i + 1))).hom x)
      exact h)
  refine ⟨f, hf, ?_⟩
  intro S F IsTrivialSum
  let := extendScalars_additive.{u, u, max v u} (algebraMap R S)
  let ηf := (exists_extendScalars_iso_localizedModuleFunctor.{u, v} (Submonoid.powers f)).some
  let E₄ : F.obj M₁ ≅ F.obj N₁ :=
    (NatIso.mapHomologicalComplex ηf (ComplexShape.up ℤ)).app M₁ ≪≫ E₃ ≪≫
      ((NatIso.mapHomologicalComplex ηf (ComplexShape.up ℤ)).app N₁).symm
  refine ⟨_, _, ⟨n, degreeN, ⟨Iso.refl _⟩⟩, ⟨m, degreeM, ⟨Iso.refl _⟩⟩, ⟨?_⟩⟩
  exact (exists_extendScalars_biprod_trivialCones_iso.{u, v} S M degreeN).some.symm ≪≫ E₄ ≪≫
    (exists_extendScalars_biprod_trivialCones_iso.{u, v} S N degreeM).some

end StacksDraft.Perfect
