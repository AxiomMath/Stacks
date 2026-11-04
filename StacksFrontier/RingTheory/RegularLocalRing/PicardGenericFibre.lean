module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.Quotient
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.Finiteness
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension

/-!
# The Picard group of the generic fibre of a flat local algebra over a valuation ring

Let `R` be a valuation ring with fraction field `K`, and let `A` be a flat local `R`-algebra,
essentially of finite type, whose special fibre `A ⊗ κ` is regular. Then the Picard group of the
generic fibre `A ⊗ K` is trivial. The proof spreads an invertible `A ⊗ K`-module out to a finite
module over a finite-type `R`-subalgebra, uses flatness over the valuation ring to make it
finitely presented, and then reduces to unique factorization on the regular special fibre.

## Main results

* `ValuationRing.subsingleton_pic_genericFibre_of_isRegular_specialFibre`: triviality of the
  Picard group of the generic fibre.

## Implementation notes

Being essentially of finite type is `Algebra.EssFiniteType`, and the special fibre is the tensor
product with the residue field of `R`; regularity of the special fibre is
`IsRegularRing`. The generic fibre is the tensor product with the fraction field rather than a
localization, which is what the spreading-out step produces.

## References

* [Stacks Project, Tag 0DLQ](https://stacks.math.columbia.edu/tag/0DLQ)
-/

namespace ValuationRing

section

universe u v w

open scoped TensorProduct

open scoped TensorProduct
open CategoryTheory

private theorem flat_of_injective_of_valuationRing {R : Type*} {M N : Type*} [CommRing R]
    [IsDomain R] [ValuationRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.IsTorsionFree R N] (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Module.Flat R M := by
  have : Module.IsTorsionFree R M := hf.moduleIsTorsionFree f (map_smul f)
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

private theorem isLocalizedModule_of_injective_of_span_eq_top {R' A' : Type*} [CommRing R']
    [CommRing A'] [Algebra R' A'] (S : Submonoid R') [IsLocalization S A'] {M L : Type*}
    [AddCommGroup M] [Module R' M] [AddCommGroup L] [Module R' L] [Module A' L]
    [IsScalarTower R' A' L] (f : M →ₗ[R'] L) (hf : Function.Injective f) {ι : Type*}
    (gens : ι → L) (hgens : Submodule.span A' (Set.range gens) = ⊤)
    (hmem : ∀ i, gens i ∈ LinearMap.range f) : IsLocalizedModule S f := by
  have hspan : Submodule.span A' (Set.range f) = ⊤ :=
    eq_top_iff.2 (hgens ▸ Submodule.span_mono (Set.range_subset_iff.2 hmem))
  refine ⟨(isLocalizedModule_id S L A').map_units, fun y => ?_,
    fun {x₁ x₂} h => ⟨1, by simp [hf h]⟩⟩
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span S A' (Set.range f) y
    (hspan ▸ Submodule.mem_top)
  obtain ⟨x, hx⟩ : t • y ∈ LinearMap.range f := by
    rwa [← LinearMap.coe_range f, Submodule.span_eq] at ht
  exact ⟨⟨x, t⟩, hx.symm⟩

private theorem finitePresentation_of_flat_of_essFiniteType {R A M : Type*} [CommRing R]
    [IsDomain R] [ValuationRing R] [CommRing A] [Algebra R A] [Algebra.EssFiniteType R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] [Module.Finite A M]
    [Module.Flat R M] : Module.FinitePresentation A M := by
  classical
  let B := Algebra.EssFiniteType.subalgebra R A
  obtain ⟨k, gens, hgens⟩ := Module.Finite.exists_fin (R := A) (M := M)
  let M₀ : Submodule B M := Submodule.span B (Set.range gens)
  have : Module.Finite B M₀ := Module.Finite.span_of_finite B (Set.finite_range gens)
  have : Module.Flat R M₀ :=
    flat_of_injective_of_valuationRing ((M₀.subtype).restrictScalars R) Subtype.val_injective
  have : Module.FinitePresentation B M₀ :=
    (finitePresentation_of_flat_of_finiteType_of_valuationRing (A := R) (B := B)
      (M := M₀)).2 this inferInstance
  have hloc : IsLocalizedModule (Algebra.EssFiniteType.submonoid R A) M₀.subtype := by
    exact isLocalizedModule_of_injective_of_span_eq_top (A' := A) _ M₀.subtype
      Subtype.val_injective gens hgens fun i => ⟨⟨gens i, Submodule.subset_span ⟨i, rfl⟩⟩, rfl⟩
  exact FinitePresentation.of_isBaseChange M₀.subtype
    ((isLocalizedModule_iff_isBaseChange (Algebra.EssFiniteType.submonoid R A) A _).mp hloc)

private theorem ker_inf_map_smul_top_eq {R A F M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup F] [Module A F] [Module R F] [IsScalarTower R A F]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] [Module.Flat R M]
    (𝔪 : Ideal R) (g : F →ₗ[A] M) (hg : Function.Surjective g) :
    LinearMap.ker g ⊓ 𝔪.map (algebraMap R A) • ⊤ = 𝔪.map (algebraMap R A) • LinearMap.ker g := by
  apply Submodule.restrictScalars_injective R
  rw [Submodule.restrictScalars_inf, Ideal.smul_restrictScalars, Ideal.smul_restrictScalars,
    Submodule.restrictScalars_top]
  exact LinearMap.ker_inf_smul_top_eq_smul_of_flat 𝔪 (g.restrictScalars R) hg

/-- Reduction modulo `I` of an `A`-linear map, as a morphism of `A ⧸ I`-modules. -/
private noncomputable def quotSMulTopMap {A : Type v} [CommRing A] (I : Ideal A) {M N : Type v}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) :
    ModuleCat.of (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)) ⟶
      ModuleCat.of (A ⧸ I) (N ⧸ I • (⊤ : Submodule A N)) :=
  ModuleCat.ofHom <| LinearMap.extendScalarsOfSurjective Ideal.Quotient.mk_surjective <|
    Submodule.mapQ _ _ f (by
      rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top)

private theorem quotSMulTopMap_mk {A : Type v} [CommRing A] (I : Ideal A) {M N : Type v}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : M →ₗ[A] N) (x : M) :
    (quotSMulTopMap I f).hom (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

private theorem quotSMulTopMap_comp_eq_zero {A : Type v} [CommRing A] (I : Ideal A)
    {M N P : Type v} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (f : M →ₗ[A] N) (g : N →ₗ[A] P) (h : g ∘ₗ f = 0) :
    quotSMulTopMap I f ≫ quotSMulTopMap I g = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk (g (f x)) = 0
  rw [← LinearMap.comp_apply, h, LinearMap.zero_apply, Submodule.Quotient.mk_zero]

private theorem shortExact_quotSMulTop {R : Type*} {A M : Type v} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [Module.Flat R M] (𝔪 : Ideal R) {k : ℕ} (g : (Fin k → A) →ₗ[A] M) (hg : Function.Surjective g) :
    (ShortComplex.mk (quotSMulTopMap (𝔪.map (algebraMap R A)) (LinearMap.ker g).subtype)
      (quotSMulTopMap (𝔪.map (algebraMap R A)) g) (quotSMulTopMap_comp_eq_zero _ _ _
        (LinearMap.exact_subtype_ker_map g).linearMap_comp_eq_zero)).ShortExact := by
  set I := 𝔪.map (algebraMap R A)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (g y) = 0 at hy
    rw [Submodule.Quotient.mk_eq_zero] at hy
    have hmap : Submodule.map g (I • ⊤) = I • (⊤ : Submodule A M) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hg]
    rw [← hmap] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    refine ⟨Submodule.Quotient.mk ⟨y - z, by simp [hzy]⟩, ?_⟩
    show Submodule.Quotient.mk (y - z) = Submodule.Quotient.mk y
    rw [Submodule.Quotient.eq]
    simpa using Submodule.neg_mem _ hz
  · rw [ModuleCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk (x : Fin k → A) = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff,
      ← ker_inf_map_smul_top_eq 𝔪 g hg]
    exact ⟨x.2, hx⟩
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
private theorem free_of_free_quotSMulTop {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [Module.FinitePresentation A M] [Module.Flat R M] (𝔪 : Ideal R)
    (hI : 𝔪.map (algebraMap R A) ≤ (⊥ : Ideal A).jacobson)
    [Module.Free (A ⧸ 𝔪.map (algebraMap R A)) (M ⧸ 𝔪.map (algebraMap R A) • (⊤ : Submodule A M))] :
    Module.Free A M := by
  classical
  set I := 𝔪.map (algebraMap R A)
  let Ā := A ⧸ I
  let b := Module.Free.chooseBasis Ā (M ⧸ I • (⊤ : Submodule A M))
  let ι := Module.Free.ChooseBasisIndex Ā (M ⧸ I • (⊤ : Submodule A M))
  choose v hv using fun i => Submodule.Quotient.mk_surjective (I • (⊤ : Submodule A M)) (b i)
  let φ : (ι → A) →ₗ[A] M := Fintype.linearCombination A v
  have hmk (a : ι → A) : Submodule.Quotient.mk (p := I • (⊤ : Submodule A M)) (φ a) =
      ∑ i, (Ideal.Quotient.mk I (a i)) • b i := by
    simp only [φ, Fintype.linearCombination_apply]
    rw [← Submodule.mkQ_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Submodule.mkQ_apply, hv]
    rfl
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hI ?_
    intro x _
    obtain ⟨c, hc⟩ : ∃ c : ι → Ā, ∑ i, c i • b i = Submodule.Quotient.mk x :=
      ⟨b.repr (Submodule.Quotient.mk x), b.sum_repr _⟩
    choose a ha using fun i => Ideal.Quotient.mk_surjective (c i)
    have hx : x - φ a ∈ I • (⊤ : Submodule A M) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hmk, ← hc]
      simp [ha]
    rw [show x = φ a + (x - φ a) by abel]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self φ a) hx
  have hker_le : LinearMap.ker φ ≤ I • LinearMap.ker φ := by
    rw [← ker_inf_map_smul_top_eq 𝔪 φ hsurj]
    refine fun a ha => ⟨ha, ?_⟩
    have h0 : ∑ i, (Ideal.Quotient.mk I (a i)) • b i = 0 := by
      rw [← hmk, (LinearMap.mem_ker.mp ha), Submodule.Quotient.mk_zero]
    have hai : ∀ i, a i ∈ I := fun i => Ideal.Quotient.eq_zero_iff_mem.mp
      (Fintype.linearIndependent_iff.mp b.linearIndependent _ h0 i)
    rw [pi_eq_sum_univ a]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hai i) Submodule.mem_top
  have hker : LinearMap.ker φ = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I _
      (Module.FinitePresentation.fg_ker φ hsurj) hker_le hI
  exact Module.Free.of_equiv
    (LinearEquiv.ofBijective φ ⟨LinearMap.ker_eq_bot.mp hker, hsurj⟩)

private theorem isStablyFree_baseChange_of_hasProjectiveDimensionLT {R : Type u} {A : Type v}
    {T : Type w}
    [CommRing R] [IsDomain R] [ValuationRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
    [Algebra.EssFiniteType R A] [CommRing T] [Algebra A T] [Module.Flat A T] (𝔪 : Ideal R)
    (hI : 𝔪.map (algebraMap R A) ≤ (⊥ : Ideal A).jacobson)
    [IsLocalRing (A ⧸ 𝔪.map (algebraMap R A))] (n : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
      [Module.Finite A M] [Module.Flat R M],
      HasProjectiveDimensionLT (ModuleCat.of (A ⧸ 𝔪.map (algebraMap R A))
        (M ⧸ 𝔪.map (algebraMap R A) • (⊤ : Submodule A M))) (n + 1) →
      Module.Projective T (T ⊗[A] M) → Module.IsStablyFree T (T ⊗[A] M) := by
  set I := 𝔪.map (algebraMap R A)
  induction n with
  | zero =>
    intro M _ _ _ _ _ _ hpd _
    have : Projective (ModuleCat.of (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M))) :=
      projective_iff_hasProjectiveDimensionLT_one.mpr hpd
    have : Module.Projective (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)) :=
      ModuleCat.projective_of_module_projective
        (ModuleCat.of (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)))
    have : Module.Free (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)) :=
      Module.free_of_flat_of_isLocalRing
    have : Module.FinitePresentation A M := finitePresentation_of_flat_of_essFiniteType (R := R)
    have : Module.Free A M := free_of_free_quotSMulTop 𝔪 hI
    infer_instance
  | succ n ih =>
    intro M _ _ _ _ _ _ hpd hproj
    obtain ⟨k, g, hg⟩ := Module.Finite.exists_fin' A M
    let N := LinearMap.ker g
    have : Module.FinitePresentation A M := finitePresentation_of_flat_of_essFiniteType (R := R)
    have : Module.Finite A N := Module.Finite.iff_fg.mpr (Module.FinitePresentation.fg_ker g hg)
    have : Module.Flat R N :=
      flat_of_injective_of_valuationRing (N.subtype.restrictScalars R) Subtype.val_injective
    have hS := shortExact_quotSMulTop 𝔪 g hg
    have : Module.Free (A ⧸ I) ((Fin k → A) ⧸ I • (⊤ : Submodule A (Fin k → A))) :=
      Module.Free.of_equiv (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
        (TensorProduct.quotTensorEquivQuotSMul (Fin k → A) I))
    have hpdN : HasProjectiveDimensionLT (ModuleCat.of (A ⧸ I)
        (N ⧸ I • (⊤ : Submodule A N))) (n + 1) := by
      refine hS.hasProjectiveDimensionLT_X₁ (n + 1) ?_ hpd
      have : HasProjectiveDimensionLT
          (ModuleCat.of (A ⧸ I) ((Fin k → A) ⧸ I • (⊤ : Submodule A (Fin k → A)))) 1 :=
        projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
      exact hasProjectiveDimensionLT_of_ge _ 1 (n + 1) (by omega)
    have hexact : Function.Exact (N.subtype.baseChange T) (g.baseChange T) :=
      Module.Flat.lTensor_exact T (LinearMap.exact_subtype_ker_map g)
    have hinj : Function.Injective (N.subtype.baseChange T) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    have hsurj : Function.Surjective (g.baseChange T) := LinearMap.lTensor_surjective _ hg
    obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (g.baseChange T) LinearMap.id hsurj
    let e := lequivProdOfRightSplitExact hinj
      (hexact.linearMap_ker_eq).symm hσ
    have : Module.Projective T ((T ⊗[A] N) × (T ⊗[A] M)) := Module.Projective.of_equiv e.symm
    have : Module.Projective T (T ⊗[A] N) :=
      Module.Projective.of_split (LinearMap.inl T _ (T ⊗[A] M)) (LinearMap.fst T _ _)
        (LinearMap.ext fun _ => rfl)
    have : Module.IsStablyFree T (T ⊗[A] N) := ih N hpdN inferInstance
    obtain ⟨Q, _, _, _, _, _⟩ := Module.IsStablyFree.exist_free_prod T (T ⊗[A] N)
    have : Module.Free T ((T ⊗[A] M) × ((T ⊗[A] N) × Q)) := by
      have e' : ((T ⊗[A] M) × ((T ⊗[A] N) × Q)) ≃ₗ[T] (T ⊗[A] (Fin k → A)) × Q :=
        (LinearEquiv.prodAssoc T _ _ _).symm.trans
          (((LinearEquiv.prodComm T _ _).trans e).prodCongr (LinearEquiv.refl T Q))
      exact Module.Free.of_equiv e'.symm
    exact Module.IsStablyFree.of_free_prod T _ ((T ⊗[A] N) × Q)

private theorem isRegularRing_quotient_map_maximalIdeal {R : Type u} {A : Type v} [CommRing R]
    [IsLocalRing R] [CommRing A] [Algebra R A]
    [IsRegularRing (A ⊗[R] IsLocalRing.ResidueField R)] :
    IsRegularRing (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) := by
  let e : (A ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) ≃+*
      A ⊗[R] IsLocalRing.ResidueField R :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor A
      (IsLocalRing.maximalIdeal R)).toRingEquiv).trans
      (Algebra.TensorProduct.comm R (R ⧸ IsLocalRing.maximalIdeal R) A).toRingEquiv
  exact IsRegularRing.of_ringEquiv e.symm

private theorem exists_ringKrullDim_le (B : Type*) [CommRing B] [IsNoetherianRing B]
    [IsLocalRing B] : ∃ d : ℕ, ringKrullDim B ≤ d := by
  have h := ringKrullDim_lt_top (R := B)
  rcases hB : ringKrullDim B with _ | _ | d
  · exact ⟨0, bot_le⟩
  · exact absurd (hB ▸ h) (lt_irrefl _)
  · exact ⟨d, le_rfl⟩

/-- **Stacks 0DLQ.** Let `R` be a valuation ring with fraction field `K`, and let `A` be a
flat local `R`-algebra, essentially of finite type, whose special fibre is regular. Then the
Picard group of the generic fibre is trivial. -/
@[stacks 0DLQ, sga "6 X 7.8" "special case"]
public theorem subsingleton_pic_genericFibre_of_isRegular_specialFibre
    {R : Type u} {A : Type v} {K : Type w}
    [CommRing R] [IsDomain R] [ValuationRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A] [IsLocalHom (algebraMap R A)]
    [Module.Flat R A] [Algebra.EssFiniteType R A]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [IsRegularRing (A ⊗[R] (IsLocalRing.ResidueField R))] :
    Subsingleton (CommRing.Pic (A ⊗[R] K))
    := by
  classical
  set 𝔪 := IsLocalRing.maximalIdeal R
  set I := 𝔪.map (algebraMap R A)
  have hIm : I ≤ IsLocalRing.maximalIdeal A := IsLocalRing.map_maximalIdeal_le _
  have hI : I ≤ (⊥ : Ideal A).jacobson := by
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top hIm)
  have : IsLocalRing (A ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have : IsRegularRing (A ⧸ I) := isRegularRing_quotient_map_maximalIdeal
  have : IsRegularLocalRing (A ⧸ I) := IsRegularLocalRing.of_isRegularRing_of_isLocalRing _
  obtain ⟨d, hd⟩ := exists_ringKrullDim_le (A ⧸ I)
  have hpd := (IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE
    hd).2
  set T := A ⊗[R] K
  let S' := Algebra.algebraMapSubmonoid A (nonZeroDivisors R)
  have : IsLocalization S' T := IsLocalization.tensor K (nonZeroDivisors R)
  have : Module.Flat A T := IsLocalization.flat T S'
  rw [CommRing.Pic.subsingleton_iff]
  intro L _ _ hL
  let _ : Module A L := Module.compHom L (algebraMap A T)
  have : IsScalarTower A T L := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let _ : Module R L := Module.compHom L (algebraMap R T)
  have : IsScalarTower R T L := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R A L := IsScalarTower.of_algebraMap_smul fun r x => by
    show algebraMap R T r • x = algebraMap A T (algebraMap R A r) • x
    rw [← IsScalarTower.algebraMap_apply]
  have : Module.IsTorsionFree R L := by
    refine ⟨fun r hr => ?_⟩
    have hr0 : r ∈ nonZeroDivisors R :=
      mem_nonZeroDivisors_of_ne_zero (isRegular_iff_ne_zero.mp hr)
    have hu : IsUnit (algebraMap R T r) := by
      rw [IsScalarTower.algebraMap_apply R A T]
      exact IsLocalization.map_units T (⟨algebraMap R A r, r, hr0, rfl⟩ : S')
    exact hu.isSMulRegular L
  obtain ⟨k, gens, hgens⟩ := Module.Finite.exists_fin (R := T) (M := L)
  let φ : (Fin k → A) →ₗ[A] L := Fintype.linearCombination A gens
  let M := (Fin k → A) ⧸ LinearMap.ker φ
  let ψ : M →ₗ[A] L := (LinearMap.ker φ).liftQ φ le_rfl
  have hψ : Function.Injective ψ :=
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  have : Module.Flat R M :=
    flat_of_injective_of_valuationRing (ψ.restrictScalars R) hψ
  have hloc : IsLocalizedModule S' ψ := by
    refine isLocalizedModule_of_injective_of_span_eq_top (A' := T) S' ψ hψ gens hgens fun i => ?_
    refine ⟨Submodule.Quotient.mk (Pi.single i 1), ?_⟩
    show φ (Pi.single i 1) = gens i
    simp [φ, Fintype.linearCombination_apply, Pi.single_apply]
  let e : T ⊗[A] M ≃ₗ[T] L :=
    ((isLocalizedModule_iff_isBaseChange S' T ψ).mp hloc).equiv
  have : Module.Projective T (T ⊗[A] M) := Module.Projective.of_equiv e.symm
  have := isStablyFree_baseChange_of_hasProjectiveDimensionLT (R := R) (T := T) 𝔪 hI d M
    (hpd (ModuleCat.of (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)))) this
  have : Module.IsStablyFree T L := Module.IsStablyFree.equiv e
  exact Module.free_of_isStablyFree_of_invertible T L

open scoped TensorProduct

end

end ValuationRing
