module

public import Mathlib
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.RingTheory.AdicCompletion.Basic

/-!
# Derived completeness of a module: the radical ideal of complete elements, and adic completeness

Let `A` be a commutative ring and `K` an object of `D(A)`. The elements `f : A` at which `K` is
derived complete, that is for which `T(K, f) = 0`, form a radical ideal of `A`. For a module `M`
regarded as a complex concentrated in degree zero this condition is a statement about the
solvability of the recurrence `aₙ - f aₙ₊₁ = bₙ` in `M`; classical `I`-adic completeness of `M`
implies it for every `f ∈ I`, and conversely, when `I` is finitely generated, derived
completeness makes `M → M^` surjective. Consequently `M` is `I`-adically complete exactly when
it is derived complete and `⋂ₙ Iⁿ M = 0`. Here `T(K, f) = 0` is `IsDerivedCompleteAt K f`, the
invertibility of `oneSubSmulShift K f : ∏ₙ K ⟶ ∏ₙ K`.

## Main results

* `exists_isRadical_ideal_isDerivedCompleteAt`: the elements at which `K` is derived complete
  form a radical ideal.
* `isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective`: adic completeness
  implies derived completeness, and for a finitely generated ideal derived completeness makes
  the completion map surjective.
* `isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot`: adic completeness
  is derived completeness together with adic separatedness.
* `homology_map_oneSubSmulShift`, `isIso_homology_map_oneSubSmulShift_iff`: the homology functor
  carries `oneSubSmulShift K f` to `oneSubSmulShift (Hⁱ K) f`, and one is an isomorphism exactly
  when the other is.
* `homologicalHomologyFunctorLinear`, `derivedHomologyFunctorLinear`: the homology functors on
  cochain complexes of `R`-modules and on `D(R)` are `R`-linear.

## References

* [The Stacks Project, Tag 091Q](https://stacks.math.columbia.edu/tag/091Q)
* [The Stacks Project, Tag 091R](https://stacks.math.columbia.edu/tag/091R)
* [The Stacks Project, Tag 091T](https://stacks.math.columbia.edu/tag/091T)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u v w

section RadicalIdeal

private lemma isUnit_one_sub_of_pow {R : Type*} [Ring R] (x : R) (n : ℕ)
    (h : IsUnit (1 - x ^ n)) : IsUnit (1 - x) := by
  have hc : Commute (1 - x) (∑ i ∈ Finset.range n, x ^ i) :=
    (mul_neg_geom_sum x n).trans (geom_sum_mul_neg x n).symm
  exact (hc.isUnit_mul_iff.mp (by rwa [mul_neg_geom_sum])).1

private lemma exists_isRadical_ideal_isUnit (A R : Type*) [CommRing A] [Ring R]
    [Algebra A R] :
    ∃ I : Ideal A, I.IsRadical ∧ ∀ f, f ∈ I ↔ ∀ t : R, IsUnit (1 - f • t) := by
  let I : Ideal A :=
    { carrier := {f | ∀ t : R, IsUnit (1 - f • t)}
      zero_mem' := by simp
      add_mem' := by
        intro f g hf hg t
        obtain ⟨u, hu⟩ := hf t
        have hv := hg (t * ↑u⁻¹)
        have he : (1 - g • (t * ↑u⁻¹)) * ↑u = 1 - (f + g) • t := by
          rw [sub_mul, one_mul, smul_mul_assoc, mul_assoc, Units.inv_mul, mul_one,
            hu, add_smul]
          abel
        exact he ▸ hv.mul u.isUnit
      smul_mem' := by
        intro a f hf t
        simpa only [smul_eq_mul, mul_smul, smul_comm a f t] using hf (a • t) }
  refine ⟨I, ?_, fun _ => Iff.rfl⟩
  rintro f ⟨n, hn⟩ t
  exact isUnit_one_sub_of_pow (f • t) n (by simpa only [smul_pow] using hn (t ^ n))

/-- The endomorphism `(aₙ) ↦ (aₙ - f aₙ₊₁)` of the module of sequences in `M`. -/
private abbrev sequenceDifference {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    (f : A) : Module.End A (ℕ → M) :=
  LinearMap.pi fun n => LinearMap.proj n - f • LinearMap.proj (n + 1)

private lemma sequenceDifference_apply {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (f : A) (x : ℕ → M) (n : ℕ) :
    sequenceDifference f x n = x n - f • x (n + 1) := rfl

private lemma sequenceDifference_bijective_pi {A M ι : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (f : A) (h : Function.Bijective (sequenceDifference (M := M) f)) :
    Function.Bijective (sequenceDifference (M := ι → M) f) := by
  classical
  constructor
  · intro x y hxy
    funext n i
    apply congr_fun (h.1 (a₁ := fun n => x n i) (a₂ := fun n => y n i) ?_) n
    exact funext fun m => congr_fun (congr_fun hxy m) i
  · intro y
    choose x hx using fun i => h.2 (fun n => y n i)
    exact ⟨fun n i => x i n, funext fun n => funext fun i => congr_fun (hx i) n⟩

private lemma isUnit_one_sub_smul_of_sequenceDifference_bijective
    {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] (f : A)
    (h : Function.Bijective (sequenceDifference (M := M) f)) (t : Module.End A M) :
    IsUnit (1 - f • t) := by
  rw [Module.End.isUnit_iff]
  constructor
  · intro x y hxy
    have he : (fun n => (t ^ n) x) = (fun n => (t ^ n) y) := by
      apply h.1
      funext n
      have hn := congr_arg (t ^ n) hxy
      simpa only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        map_sub, map_smul, sequenceDifference_apply, pow_succ, Module.End.mul_apply] using hn
    simpa using congr_fun he 0
  · intro y
    obtain ⟨x, hx⟩ := h.2 (fun n => (t ^ n) y)
    have hs : (fun n => t (x n)) = (fun n => x (n + 1)) := by
      apply h.1
      funext n
      change t (x n) - f • t (x (n + 1)) = x (n + 1) - f • x (n + 1 + 1)
      rw [← map_smul, ← map_sub, ← sequenceDifference_apply, congr_fun hx,
        ← sequenceDifference_apply, congr_fun hx, pow_succ', Module.End.mul_apply]
    refine ⟨x 0, ?_⟩
    change x 0 - f • t (x 0) = y
    rw [congr_fun hs 0]
    simpa only [sequenceDifference_apply, pow_zero, Module.End.one_apply] using congr_fun hx 0

private lemma exists_isRadical_ideal_sequenceDifference (A M : Type*) [CommRing A]
    [AddCommGroup M] [Module A M] :
    ∃ I : Ideal A, I.IsRadical ∧ ∀ f, f ∈ I ↔
      Function.Bijective (sequenceDifference (M := M) f) := by
  obtain ⟨I, hI, hmem⟩ := exists_isRadical_ideal_isUnit A (Module.End A (ℕ → M))
  refine ⟨I, hI, fun f => (hmem f).trans ⟨fun h => ?_, fun h =>
    isUnit_one_sub_smul_of_sequenceDifference_bijective f (sequenceDifference_bijective_pi f h)⟩⟩
  exact (Module.End.isUnit_iff _).mp (h (LinearMap.pi fun n => LinearMap.proj (n + 1)))

private lemma isIso_iff_bijective_postcomp {C : Type*} [Category C] {P : C} (d : P ⟶ P) :
    IsIso d ↔ Function.Bijective (fun a : P ⟶ P => a ≫ d) := by
  refine ⟨fun h => (isIso_iff_yoneda_map_bijective d).1 h P, fun h => ?_⟩
  obtain ⟨e, he⟩ := h.2 (𝟙 P)
  refine ⟨e, h.1 ?_, he⟩
  simp only [Category.assoc, he, Category.comp_id, Category.id_comp]

private lemma isIso_oneSubSmulShift_iff_bijective {A C : Type*} [CommRing A] [Category C]
    [Preadditive C] [Linear A C] [HasProductsOfShape ℕ C] (K : C) (f : A) :
    IsIso (oneSubSmulShift K f) ↔
      Function.Bijective (sequenceDifference (M := ((∏ᶜ fun _ : ℕ => K) ⟶ K)) f) := by
  let P := ∏ᶜ fun _ : ℕ => K
  let d : P ⟶ P := oneSubSmulShift K f
  let e : (ℕ → (P ⟶ K)) ≃ (P ⟶ P) :=
    { toFun := Pi.lift
      invFun := fun a n => a ≫ Pi.π (fun _ : ℕ => K) n
      left_inv := by intro x; funext n; simp
      right_inv := by intro a; apply Pi.hom_ext; intro n; simp }
  have he (x : ℕ → (P ⟶ K)) : e (sequenceDifference f x) = e x ≫ d := by
    apply Pi.hom_ext
    intro n
    simp [e, d, Preadditive.comp_sub]
  have hd : (fun a : P ⟶ P => a ≫ d) = e ∘ sequenceDifference f ∘ e.symm := by
    funext a
    simp only [Function.comp_apply, he, e.apply_symm_apply]
  change IsIso d ↔ _
  rw [isIso_iff_bijective_postcomp, hd, Equiv.comp_bijective, Equiv.bijective_comp]

/-- For `K ∈ D(A)`, the elements `f : A` at which `K` is derived complete —
equivalently, for which the derived limit of `⋯ → K → K`, with every transition map
multiplication by `f`, is zero — are precisely the elements of a radical ideal of `A`. -/
@[stacks 091Q]
public theorem exists_isRadical_ideal_isDerivedCompleteAt (A : Type u) [CommRing A]
    (K : DerivedCategory (ModuleCat.{v} A))
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] :
    ∃ I : Ideal A, I.IsRadical ∧ ∀ f : A, f ∈ I ↔ IsDerivedCompleteAt K f := by
  obtain ⟨I, hI, hmem⟩ := exists_isRadical_ideal_sequenceDifference A
    ((∏ᶜ fun _ : ℕ => K) ⟶ K)
  exact ⟨I, hI, fun f => (hmem f).trans (isIso_oneSubSmulShift_iff_bijective K f).symm⟩

end RadicalIdeal

section Adic

private lemma pow_smul_mem_pow_smul_top {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) {f : A} (hf : f ∈ I) (n : ℕ) (x : M) :
    f ^ n • x ∈ I ^ n • (⊤ : Submodule A M) :=
  Submodule.smul_mem_smul (Ideal.pow_mem_pow hf n) Submodule.mem_top

private lemma sum_pow_smul_smodEq {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) {f : A} (hf : f ∈ I) (a : ℕ → M)
    {m n : ℕ} (hmn : m ≤ n) :
    (∑ k ∈ Finset.range m, f ^ k • a k) ≡
      (∑ k ∈ Finset.range n, f ^ k • a k) [SMOD I ^ m • (⊤ : Submodule A M)] := by
  rw [SModEq.sub_mem, ← Finset.sum_range_add_sum_Ico _ hmn]
  simp only [sub_add_cancel_left]
  exact Submodule.neg_mem _ (Submodule.sum_mem _ fun k hk => Submodule.smul_mono_left
    (Ideal.pow_le_pow_right (Finset.mem_Ico.mp hk).1) (pow_smul_mem_pow_smul_top I hf k _))

private lemma exists_sum_pow_smul_limit {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) [IsPrecomplete I M] {f : A} (hf : f ∈ I)
    (a : ℕ → M) :
    ∃ L : M, ∀ n, (∑ k ∈ Finset.range n, f ^ k • a k) ≡ L
      [SMOD I ^ n • (⊤ : Submodule A M)] :=
  IsPrecomplete.prec inferInstance (fun hmn => sum_pow_smul_smodEq I hf a hmn)

private lemma sum_pow_smul_shift {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (f : A) (a : ℕ → M) (i n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), f ^ k • a (i + k)) =
      a i + f • ∑ k ∈ Finset.range n, f ^ k • a (i + 1 + k) := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_smul, Nat.add_zero, Finset.smul_sum, pow_succ', mul_smul]
  rw [add_comm]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by simp only [Nat.add_comm, Nat.add_left_comm]

private lemma recurrence_bijective_of_isAdicComplete {A M : Type*}
    [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) [IsAdicComplete I M] {f : A} (hf : f ∈ I) :
    Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1)) := by
  constructor
  · intro a b hab
    have hrec (n : ℕ) : a n - b n = f • (a (n + 1) - b (n + 1)) := by
      have := congr_fun hab n
      dsimp at this
      rw [smul_sub]
      exact sub_eq_sub_iff_sub_eq_sub.mp this
    have hpow (n k : ℕ) : a n - b n = f ^ k • (a (n + k) - b (n + k)) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [ih, hrec (n + k), ← mul_smul, ← pow_succ]
        congr 2
    funext n
    apply sub_eq_zero.mp
    apply IsHausdorff.haus' (I := I)
    intro k
    rw [SModEq.sub_mem, sub_zero, hpow n k]
    exact pow_smul_mem_pow_smul_top I hf k _
  · intro a
    choose L hL using fun i => exists_sum_pow_smul_limit I hf (fun k => a (i + k))
    refine ⟨L, funext fun i => ?_⟩
    apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
    intro n
    have h₁ := (hL i (n + 1)).mono
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)))
    have h₂ := (hL (i + 1) n).smul f
    have h := h₁.symm.sub h₂.symm
    rw [sum_pow_smul_shift] at h
    simpa only [add_sub_cancel_right] using h

private lemma isPrecomplete_span_singleton_of_recurrence_surjective {A M : Type*}
    [CommRing A] [AddCommGroup M] [Module A M] (f : A)
    (hs : Function.Surjective (fun a : ℕ → M => fun n => a n - f • a (n + 1))) :
    IsPrecomplete (Ideal.span {f}) M := by
  constructor
  intro g hg
  have hd (n : ℕ) : ∃ a : M, f ^ n • a = g (n + 1) - g n := by
    have h := (hg (Nat.le_succ n)).symm
    rw [SModEq.sub_mem, Ideal.span_singleton_pow,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
    obtain ⟨a, _, ha⟩ := h
    exact ⟨a, ha⟩
  choose a ha using hd
  obtain ⟨b, hb⟩ := hs a
  have htel (n : ℕ) : g n - g 0 = b 0 - f ^ n • b n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have he : b n - f • b (n + 1) = a n := congr_fun hb n
      have he' := congr_arg (fun x : M => f ^ n • x) he
      rw [smul_sub, ← mul_smul, ← pow_succ, ha n] at he'
      calc
        g (n + 1) - g 0 = (g n - g 0) + (g (n + 1) - g n) := by abel
        _ = _ := by rw [ih, ← he']; abel
  refine ⟨g 0 + b 0, fun n => ?_⟩
  rw [SModEq.sub_mem]
  have he : g n - (g 0 + b 0) = -(f ^ n • b n) := by
    calc
      g n - (g 0 + b 0) = (g n - g 0) - b 0 := by abel
      _ = _ := by rw [htel]; abel
  rw [he]
  exact Submodule.neg_mem _
    (pow_smul_mem_pow_smul_top _ (Ideal.subset_span (Set.mem_singleton f)) n _)

/-- Countable products of `R`-modules are exact. -/
local instance (R : Type*) [CommRing R] :
    HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{w} R) :=
  moduleCat_hasExactLimitsOfShape_discrete.{w} R ℕ

/-- The derived category of `R`-modules has countable products. -/
local instance (R : Type*) [CommRing R] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{w} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

section Products

/-- The homology functor on cochain complexes of `R`-modules is `R`-linear. -/
public theorem homologicalHomologyFunctorLinear
    {R : Type u} [CommRing R] (i : ℤ) :
    Functor.Linear R
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) i) where
  map_smul f r := by
    change ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) i).map
        (r • f)) = _
    rw [show (HomologicalComplex.shortComplexFunctor (ModuleCat.{w} R)
      (ComplexShape.up ℤ) i).map (r • f) = r •
        (HomologicalComplex.shortComplexFunctor (ModuleCat.{w} R)
          (ComplexShape.up ℤ) i).map f by rfl]
    apply ShortComplex.homologyMap_smul

attribute [local instance] homologicalHomologyFunctorLinear

/-- The homology functor on `D(R)` is `R`-linear. -/
public theorem derivedHomologyFunctorLinear
    {R : Type u} [CommRing R] (i : ℤ) :
    Functor.Linear R (DerivedCategory.homologyFunctor (ModuleCat.{w} R) i) := by
  let : Localization.Lifting
      (DerivedCategory.Q (C := ModuleCat.{w} R))
      (HomologicalComplex.quasiIso (ModuleCat.{w} R) (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) i)
      (DerivedCategory.homologyFunctor (ModuleCat.{w} R) i) :=
    ⟨DerivedCategory.homologyFunctorFactors (ModuleCat.{w} R) i⟩
  exact (Localization.functor_linear_iff
    (DerivedCategory.Q (C := ModuleCat.{w} R))
    (HomologicalComplex.quasiIso (ModuleCat.{w} R) (ComplexShape.up ℤ)) R
    (HomologicalComplex.homologyFunctor (ModuleCat.{w} R) (ComplexShape.up ℤ) i)
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) i)).mp inferInstance

attribute [local instance] derivedHomologyFunctorLinear

/-- The homology functor carries `oneSubSmulShift K f` to `oneSubSmulShift (Hⁱ K) f`, via the
comparison map with the product of the homologies. -/
public theorem homology_map_oneSubSmulShift (R : Type*) [CommRing R]
    (K : DerivedCategory (ModuleCat.{w} R)) (f : R) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).map (oneSubSmulShift K f) ≫
        piComparison (DerivedCategory.homologyFunctor (ModuleCat.{w} R) i)
          (fun _ : ℕ => K) =
      piComparison (DerivedCategory.homologyFunctor (ModuleCat.{w} R) i)
          (fun _ : ℕ => K) ≫
        oneSubSmulShift ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj K) f := by
  apply limit.hom_ext
  rintro ⟨n⟩
  simp [oneSubSmulShift, milnorMap, Category.assoc]

/-- `Hⁱ(oneSubSmulShift K f)` is an isomorphism exactly when `oneSubSmulShift (Hⁱ K) f` is. -/
public theorem isIso_homology_map_oneSubSmulShift_iff (R : Type*) [CommRing R]
    (K : DerivedCategory (ModuleCat.{w} R)) (f : R) (i : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).map
      (oneSubSmulShift K f)) ↔
      IsIso (oneSubSmulShift
        ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj K) f) := by
  let c := piComparison (DerivedCategory.homologyFunctor (ModuleCat.{w} R) i)
    (fun _ : ℕ => K)
  have : IsIso c := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor _ _
  rw [← isIso_comp_right_iff _ c, homology_map_oneSubSmulShift,
    isIso_comp_left_iff c]

private lemma isIso_oneSubSmulShift_module_iff (A : Type*) [CommRing A]
    (M : ModuleCat.{w} A) (f : A) :
    IsIso (oneSubSmulShift M f) ↔
      Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1)) := by
  let e := ModuleCat.piIsoPi (fun _ : ℕ => M)
  let d := ModuleCat.ofHom (sequenceDifference (M := M) f)
  have h : e.inv ≫ oneSubSmulShift M f = d ≫ e.inv := by
    apply Pi.hom_ext
    intro n
    simp only [oneSubSmulShift, milnorMap, e, Category.assoc, Pi.lift_comp_π,
      Preadditive.comp_sub, Linear.comp_smul, Category.comp_id,
      ModuleCat.piIsoPi_inv_kernel_ι]
    ext a
    rfl
  rw [← isIso_comp_left_iff e.inv, h, isIso_comp_right_iff,
    ConcreteCategory.isIso_iff_bijective]
  rfl

private lemma isIso_oneSubSmulShift_iff_of_iso (R : Type*) [CommRing R]
    (C : Type*) [Category C] [Preadditive C] [Linear R C] [HasProductsOfShape ℕ C]
    {K K' : C} (e : K ≅ K') (f : R) :
    IsIso (oneSubSmulShift K f) ↔ IsIso (oneSubSmulShift K' f) := by
  have : IsIso (Limits.Pi.map (fun _ : ℕ => e.hom)) := inferInstance
  rw [← isIso_comp_right_iff _ (Limits.Pi.map (fun _ : ℕ => e.hom)),
    oneSubSmulShift_naturality, isIso_comp_left_iff]

private lemma isIso_oneSubSmulShift_single_iff (A : Type*) [CommRing A]
    (M : ModuleCat.{w} A) (f : A) :
    IsIso (oneSubSmulShift ((DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M) f) ↔
      Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1)) := by
  let K := (DerivedCategory.singleFunctor (ModuleCat.{w} A) 0).obj M
  let e := (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{w} A) 0).app M
  have hzero : IsIso (oneSubSmulShift
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) 0).obj K) f) ↔
      Function.Bijective (fun a : ℕ → M => fun n => a n - f • a (n + 1)) :=
    (isIso_oneSubSmulShift_iff_of_iso A _ e f).trans (isIso_oneSubSmulShift_module_iff A M f)
  rw [DerivedCategory.isIso_iff]
  refine ⟨fun h => hzero.mp ((isIso_homology_map_oneSubSmulShift_iff A K f 0).mp (h 0)),
    fun h n => ?_⟩
  apply (isIso_homology_map_oneSubSmulShift_iff A K f n).mpr
  by_cases hn : n = 0
  · subst n
    exact hzero.mpr h
  · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) n).obj K) := by
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact DerivedCategory.isZero_of_isGE K 0 n hn
      · exact DerivedCategory.isZero_of_isLE K 0 n hn
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    apply (isIso_oneSubSmulShift_module_iff A _ f).mpr
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun a => ⟨a, Subsingleton.elim _ _⟩⟩

end Products

/-- An `I`-adically complete module is derived complete with respect to `I`. Conversely, for a
finitely generated ideal `I`, derived completeness makes the canonical map to the `I`-adic
completion surjective. -/
@[stacks 091R]
public theorem isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective
    (A : Type u) [CommRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] :
    (IsAdicComplete I M → IsDerivedCompleteModule I (ModuleCat.of A M)) ∧
      (I.FG → IsDerivedCompleteModule I (ModuleCat.of A M) →
        Function.Surjective (AdicCompletion.of I M)) := by
  constructor
  · intro hc f hf
    let := hc
    exact (isIso_oneSubSmulShift_single_iff A (ModuleCat.of A M) f).mpr
      (recurrence_bijective_of_isAdicComplete I hf)
  · intro hfg hv
    obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
    apply adicCompletion_of_surjective_of_forall_span_singleton_surjective M g _ I hg.symm
    intro i
    have hgi : g i ∈ I := hg ▸ Ideal.subset_span (Set.mem_range_self i)
    have hb := (isIso_oneSubSmulShift_single_iff A (ModuleCat.of A M) (g i)).mp
      (hv (g i) hgi)
    let : IsPrecomplete (Ideal.span {g i}) M :=
      isPrecomplete_span_singleton_of_recurrence_surjective (g i) hb.2
    exact AdicCompletion.of_surjective _ M

private theorem ker_adicCompletion_of_eq_iInf_pow_smul_top
    (A : Type u) [CommRing A] (I : Ideal A)
    (M : Type v) [AddCommGroup M] [Module A M] :
    LinearMap.ker (AdicCompletion.of I M) =
      ⨅ n : ℕ, I ^ n • (⊤ : Submodule A M) := by
  ext x
  simp [AdicCompletion.ext_iff, AdicCompletion.of_apply,
    Submodule.Quotient.mk_eq_zero]

/-- For a finitely generated ideal `I`, an `A`-module `M` is `I`-adically complete if and only
if it is derived complete with respect to `I` and the intersection of the submodules `I ^ n M`
is zero. -/
@[stacks 091T]
public theorem isAdicComplete_iff_isDerivedCompleteModule_and_iInf_pow_smul_top_eq_bot
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : Type v) [AddCommGroup M] [Module A M]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))] :
    IsAdicComplete I M ↔
      IsDerivedCompleteModule I (ModuleCat.of A M) ∧
        ⨅ n : ℕ, I ^ n • (⊤ : Submodule A M) = ⊥ := by
  let hR := isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective A I M
  constructor
  · intro h
    refine ⟨hR.1 h, ?_⟩
    rw [← ker_adicCompletion_of_eq_iInf_pow_smul_top A I M,
      LinearMap.ker_eq_bot]
    exact (AdicCompletion.of_bijective_iff.mpr h).1
  · rintro ⟨hderived, hseparated⟩
    rw [← AdicCompletion.of_bijective_iff]
    refine ⟨?_, hR.2 hI hderived⟩
    rwa [← LinearMap.ker_eq_bot, ker_adicCompletion_of_eq_iInf_pow_smul_top A I M]

end Adic

end

end
