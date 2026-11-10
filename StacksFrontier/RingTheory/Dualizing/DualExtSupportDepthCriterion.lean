module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Homology.ExtendScalars.Flat
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Depth.Defs.Defs
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.DerivedLocalization
public import StacksFrontier.RingTheory.Dualizing.DimensionFunctionSpecialization
public import StacksFrontier.RingTheory.Dualizing.DualExtDepthDimension
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.ExtSupportBound
public import StacksFrontier.RingTheory.Dualizing.FiniteDimension
public import StacksFrontier.RingTheory.Dualizing.LocalizedExt
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
public import StacksFrontier.RingTheory.Equidimensional.FlatLocal
public import StacksFrontier.RingTheory.KrullDimension.Defs
public import StacksFrontier.RingTheory.Support.Basic
public import StacksFrontier.Topology.Dimension.CatenaryOfDimensionFunction
public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference

import all StacksFrontier.RingTheory.Dualizing.FiniteDimension

/-!
# The support of the partial sums of the dual Ext modules

Let `(A, 𝔪)` be a Noetherian local ring with a normalized dualizing complex `ω_A^•`, let `M` be
a finite `A`-module, and write `Eⁱ = Ext_A^{-i}(M, ω_A^•)`. A prime `𝔭` of `A` lies in the
support of the finite direct sum `E⁰ ⊕ E¹ ⊕ ⋯ ⊕ Eⁱ` exactly when

`depth_{A_𝔭}(M_𝔭) + dim(A / 𝔭) ≤ i`.

The proof localizes at `𝔭`: the formation of the dual Ext modules commutes with localization,
and the localization of `ω_A^•` becomes normalized over `A_𝔭` after a shift by `dim(A / 𝔭)`,
because the dimension function of a dualizing complex over a local ring takes the value
`dim(A / 𝔭)` at `𝔭`. Under that shift the degrees `0, …, i` of the global Ext modules become the
degrees `0, …, i - dim(A/𝔭)` of the dual Ext modules of `M_𝔭`, and the least degree in which the
latter are nonzero is the depth of `M_𝔭`.

## Main definitions

* `Dualizing.pseudoCoherenceLocalizationDerivedNatIso` — the derived extension of scalars along
  `A → A_𝔭` that the dimension function of a dualizing complex is phrased through, identified as
  a functor with the functor induced on derived categories by localization of modules at `𝔭`;
  and `Dualizing.pseudoCoherenceLocalizationDerivedObjIso`, that isomorphism at a single object.

## Main results

* `Dualizing.mem_support_pi_moduleExtInto_iff_depth_add_ringKrullDim_le` — the characterisation
  of the primes in the support of `E⁰ ⊕ ⋯ ⊕ Eⁱ`.
* `Dualizing.exists_isGE_of_isNormalizedDualizingComplex` — a normalized dualizing complex is
  bounded below.
* `Dualizing.isNormalizedDualizingComplex_localizedModule_shift` — [Stacks, Tag 0A7Z] in the
  `ModuleCat.localizedModuleFunctor` spelling: `(ω^•_A)_𝔭[-dim(A/𝔭)]` is a normalized dualizing
  complex over `A_𝔭`.
* `Dualizing.pseudoCoherenceLocalizationDerivedObjIso_naturality` — that object-wise isomorphism is
  natural, being a component of the isomorphism of functors.

## Implementation notes

The finite direct sum `E⁰ ⊕ ⋯ ⊕ Eⁱ` is the dependent product indexed by `Fin (i + 1)`, which is
the same module. Depth takes values in `ℕ∞` and the Krull dimension of `A / 𝔭` in `WithBot ℕ∞`,
so the depth is coerced into `WithBot ℕ∞` in the sum; the dimension is a natural number because
a Noetherian local ring has finite Krull dimension, and the depth is allowed to be `⊤`, in which
case the inequality fails for every `i`, matching the vanishing of all the `Eⁱ` after
localization.

Localization of the derived category is taken to be the functor induced by the exact functor
`ModuleCat.localizedModuleFunctor`; the dimension function of a dualizing complex is phrased
through derived extension of scalars, and the two are identified by comparing both with the
derived functor of `ModuleCat.extendScalars`, which is the left derived functor of a flat,
hence exact, functor.

## References

* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

/-! ### Comparing extension of scalars with localization -/

/-- **The derived extension of scalars of `StacksDraft.PseudoCoherence` along `A → A_𝔭`**, which
is the localization used by the dimension function of a dualizing complex, agrees as a functor
with the functor induced on derived categories by localization of modules at `𝔭`. -/
public noncomputable def pseudoCoherenceLocalizationDerivedNatIso
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] :
    StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime p)) ≅
      (ModuleCat.localizedModuleFunctor.{max v u} p.primeCompl).mapDerivedCategory := by
  let R := Localization.AtPrime p
  let f := algebraMap A R
  let F := ModuleCat.extendScalars.{u, u, max v u} f
  let U := ModuleCat.uliftFunctor.{u, max v u, u} A
  let G := ModuleCat.localizedModuleFunctor.{max v u} p.primeCompl
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, max v u} f
  let W := HomologicalComplex.quasiIso (ModuleCat.{max v u} A) (ComplexShape.up ℤ)
  letI : F.Additive := (ModuleCat.extendRestrictScalarsAdj f).left_adjoint_additive
  letI : Limits.PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat' f
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat R p.primeCompl))
  letI : Limits.PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj f).leftAdjoint_preservesColimits
  letI : Limits.PreservesFiniteColimits F :=
    Limits.PreservesColimitsOfSize.preservesFiniteColimits F
  letI : U.Additive := inferInstance
  letI : Limits.PreservesFiniteLimits U := inferInstance
  letI : Limits.PreservesFiniteColimits U := inferInstance
  letI : G.Additive := inferInstance
  letI : Limits.PreservesFiniteLimits G := inferInstance
  letI : Limits.PreservesFiniteColimits G := inferInstance
  letI : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W F.mapDerivedCategory F.mapDerivedCategoryFactors
  let comparison : DerivedCategory.Q ⋙ D.functor ⟶
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := D.comparison
  have : D.functor.IsLeftDerivedFunctor comparison W := D.isLeftDerived
  let eFD : F.mapDerivedCategory ≅ D.functor :=
    Functor.leftDerivedUnique (LF := F.mapDerivedCategory) (LF' := D.functor)
    (α := F.mapDerivedCategoryFactors.hom) (α'₂ := comparison) (W := W)
  let ηU : U ≅ 𝟭 (ModuleCat.{max v u} A) :=
    NatIso.ofComponents (fun M => (ULift.moduleEquiv.{u, max v u, u} :
      ULift.{u, max v u} (M : Type (max v u)) ≃ₗ[A] (M : Type (max v u))).toModuleIso)
      (by
        intro M N g
        apply ModuleCat.hom_ext
        ext x
        rfl)
  let ηUF : U ⋙ F ≅ G := Functor.isoWhiskerRight ηU F ≪≫ Functor.leftUnitor F ≪≫
    extendScalarsIsoLocalizedModuleFunctor.{u, v} p.primeCompl
  exact Functor.isoWhiskerLeft U.mapDerivedCategory eFD.symm ≪≫
    (mapDerivedCategoryComp U F).symm ≪≫
    mapDerivedCategoryNatIso (U ⋙ F) G ηUF

/-- The derived extension of scalars of `StacksDraft.PseudoCoherence` along `A → A_𝔭`, read at a
single object of the derived category. -/
public noncomputable def pseudoCoherenceLocalizationDerivedObjIso
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max v u} A)) :
    (StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime p))).obj K ≅
      (ModuleCat.localizedModuleFunctor.{max v u} p.primeCompl).mapDerivedCategory.obj K :=
  (pseudoCoherenceLocalizationDerivedNatIso.{u, v} p).app K

/-- The derived extension of scalars of `StacksDraft.PseudoCoherence` along `A → A_𝔭`, which is
the localization used by the dimension function of a dualizing complex, agrees with the functor
induced on derived categories by localization of modules at `𝔭`. This is
`Dualizing.pseudoCoherenceLocalizationDerivedObjIso`. -/
private noncomputable def pseudoCoherenceLocalizationDerivedIso
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{max v u} A)) :
    (StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A (Localization.AtPrime p))).obj K ≅
      (ModuleCat.localizedModuleFunctor.{max v u} p.primeCompl).mapDerivedCategory.obj K :=
  pseudoCoherenceLocalizationDerivedObjIso.{u, v} p K


/-- `Dualizing.pseudoCoherenceLocalizationDerivedObjIso` is natural in the object of the derived
category, being a component of `Dualizing.pseudoCoherenceLocalizationDerivedNatIso`. -/
public theorem pseudoCoherenceLocalizationDerivedObjIso_naturality
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    {K L : DerivedCategory (ModuleCat.{max v u} A)} (g : K ⟶ L) :
    (StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap A (Localization.AtPrime p))).map g ≫
        (pseudoCoherenceLocalizationDerivedObjIso.{u, v} p L).hom =
      (pseudoCoherenceLocalizationDerivedObjIso.{u, v} p K).hom ≫
        (ModuleCat.localizedModuleFunctor.{max v u} p.primeCompl).mapDerivedCategory.map g :=
  (pseudoCoherenceLocalizationDerivedNatIso.{u, v} p).hom.naturality g

/-! ### Localization of the dual Ext modules -/

/-- Localization commutes with a finite product of modules. -/
private noncomputable def localizedPiEquiv
    {R : Type u} [CommRing R] {ι : Type*} [Fintype ι]
    (S : Submonoid R) (M : ι → Type*)
    [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)] :
    LocalizedModule S (∀ j, M j) ≃ₗ[R]
      (∀ j, LocalizedModule S (M j)) := by
  classical
  let f : (∀ j, M j) →ₗ[R] (∀ j, LocalizedModule S (M j)) :=
    LinearMap.pi fun j => (LocalizedModule.mkLinearMap S (M j)).comp (LinearMap.proj j)
  letI : IsLocalizedModule S f := by
    dsimp [f]
    exact IsLocalizedModule.pi S (fun j => LocalizedModule.mkLinearMap S (M j))
  exact IsLocalizedModule.linearEquiv S (LocalizedModule.mkLinearMap S (∀ j, M j)) f

/-- A product of modules is nontrivial exactly when one of its factors is. -/
private lemma nontrivial_pi_iff_exists
    {ι : Type*} (M : ι → Type*) [∀ j, Nonempty (M j)] :
    Nontrivial (∀ j, M j) ↔ ∃ j, Nontrivial (M j) := by
  classical
  constructor
  · intro h
    by_contra hn
    push Not at hn
    let (j : ι) : Subsingleton (M j) := hn j
    exact not_nontrivial_iff_subsingleton.mpr (inferInstance : Subsingleton (∀ j, M j)) h
  · rintro ⟨j, hj⟩
    exact @Pi.nontrivial_at ι M j _ hj

/-! ### Normalization after localization -/

/-- On the spectrum of a Noetherian local ring, a dimension function vanishing at the closed
point takes the value `dim(A / 𝔭)` at a prime `𝔭`. -/
private lemma dimensionFunction_eq_quotientDimension
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (δ : TopologicalSpace.DimensionFunction (PrimeSpectrum A))
    (hδm : δ ⟨IsLocalRing.maximalIdeal A,
      (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩ = 0)
    (p : Ideal A) [p.IsPrime] (e : ℕ)
    (he : ringKrullDim (A ⧸ p) = e) : δ ⟨p, inferInstance⟩ = (e : ℤ) := by
  let hSober : StacksSober (PrimeSpectrum A) :=
    stacksSober_iff_t0_and_quasiSober.mpr ⟨inferInstance, inferInstance⟩
  have hδcat : IsDimensionFunctionForCatenary (δ : PrimeSpectrum A → ℤ) := by
    refine ⟨?_, ?_⟩
    · intro x y hxy hne
      exact δ.strictAnti_specializes hxy hne
    · intro x y himm
      exact δ.step_immediate himm
  have hcat := isCatenary_of_isSober_of_dim hSober δ hδcat
  have hdimFn : ∃ δ' : TopologicalSpace.DimensionFunction (PrimeSpectrum A),
      ∀ q, δ' q = deltaDim q := by
    apply (TopologicalSpace.exists_dimensionFunction_iff deltaDim).2
    refine ⟨deltaDim_lt_of_specializes, ?_⟩
    intro x y himm
    apply (deltaDim_eq_iff_coheight x y).2
    exact FlatLocalCatenary.coheight_covBy_of_isCatenarySpace hcat x y
      ((immediateSpec_iff_covby x y).mp himm)
  obtain ⟨δ', hδ'⟩ := hdimFn
  let m : PrimeSpectrum A := ⟨IsLocalRing.maximalIdeal A,
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime⟩
  let q : PrimeSpectrum A := ⟨p, inferInstance⟩
  have hqm : q ≤ m := by
    change p ≤ IsLocalRing.maximalIdeal A
    exact IsLocalRing.le_maximalIdeal_of_isPrime p
  have hspec : q ⤳ m := (PrimeSpectrum.le_iff_specializes q m).mp hqm
  have hdiff := TopologicalSpace.DimensionFunction.sub_eq_of_specializes δ δ' hspec
  have hmmax : IsMax m := by
    intro r hmr
    change r.asIdeal ≤ IsLocalRing.maximalIdeal A
    exact IsLocalRing.le_maximalIdeal_of_isPrime r.asIdeal
  have hδ'm : δ' m = 0 := by
    rw [hδ' m, deltaDim, dimQuotient, Order.coheight_eq_zero.mpr hmmax]
    rfl
  have hδq : δ q = δ' q := by
    have h0 : δ q - δ' q = 0 := by
      rw [hdiff, hδm, hδ'm]
      ring
    omega
  rw [hδq, hδ' q, deltaDim, dimQuotient]
  have hco : Order.coheight q = (e : ℕ∞) := by
    exact_mod_cast (coheight_eq_ringKrullDim_quotient q).trans he
  rw [hco]
  norm_num

/-- **A normalized dualizing complex is bounded below.**  It has finite injective amplitude, and a
complex of finite injective amplitude is bounded on both sides.

This is what `Dualizing.localizedExtLinearEquivOfDerivedHom` and its naturality ask for as
`hKge`. -/
theorem exists_isGE_of_isNormalizedDualizingComplex {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K) : ∃ b : ℤ, K.IsGE b := by
  obtain ⟨a, b, hAmp⟩ := hK.1.finiteInjectiveDimension
  exact ⟨a, (isGE_isLE_of_hasInjectiveAmplitude.{u, v} K a b hAmp).1⟩

/-- **Normalization after localization.** Localizing a normalized dualizing complex over a
Noetherian local ring at a prime `𝔭` and shifting by `-dim(A / 𝔭)` gives a normalized dualizing
complex over `A_𝔭`. -/
private theorem isNormalizedDualizingComplex_localized_shift
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K)
    (p : Ideal A) [p.IsPrime] (e : ℕ) (he : ringKrullDim (A ⧸ p) = e) :
    IsNormalizedDualizingComplex.{u, v}
      (((ModuleCat.localizedModuleFunctor.{max v u} p.primeCompl).mapDerivedCategory.obj
        K)⟦-(e : ℤ)⟧) := by
  have hδ : dualizingDimension.{u, v} K ⟨p, inferInstance⟩ = (e : ℤ) :=
    dimensionFunction_eq_quotientDimension (dualizingDimensionFunction.{u, v} K hK.1)
      (dualizingDimension_maximalIdeal_eq_zero.{u, v} K hK) p e he
  have hspec := dualizingDimension_spec.{u, v} K hK.1 ⟨p, inferInstance⟩
  rw [hδ] at hspec
  exact (isNormalizedDualizingComplex_congr.{u, v}
    ((shiftFunctor (DerivedCategory (ModuleCat.{max v u} (Localization.AtPrime p)))
      (-(e : ℤ))).mapIso (pseudoCoherenceLocalizationDerivedObjIso.{u, v} p K))).mp hspec

/-- **Normalization after localization**, [Stacks, Tag 0A7Z] in the
`ModuleCat.localizedModuleFunctor` spelling. Localizing a normalized dualizing complex over a
Noetherian local ring at a prime `𝔭` and shifting by `-dim(A / 𝔭)` gives a normalized dualizing
complex over `A_𝔭`. -/
alias isNormalizedDualizingComplex_localizedModule_shift :=
  isNormalizedDualizingComplex_localized_shift

/-! ### Arithmetic and vanishing lemmas -/

/-- An infimum over the degrees satisfying a predicate, increased by `e`, is at most `i` exactly
when some degree satisfying the predicate is at most `i - e`. -/
private lemma iInf_nat_add_le_iff (P : ℕ → Prop) (e i : ℕ) :
    (⨅ n : ℕ, ⨅ (_ : P n), (n : ℕ∞)) + (e : ℕ∞) ≤ (i : ℕ∞) ↔
      ∃ n, P n ∧ n + e ≤ i := by
  classical
  constructor
  · intro hi
    by_contra hno
    have hbound : ((i + 1 - e : ℕ) : ℕ∞) ≤
        ⨅ n : ℕ, ⨅ (_ : P n), (n : ℕ∞) := by
      refine le_iInf fun n => le_iInf fun hn => ?_
      have hn' : i + 1 - e ≤ n := by
        by_contra hlt
        exact hno ⟨n, hn, by omega⟩
      exact_mod_cast hn'
    have hnat : i + 1 ≤ i + 1 - e + e := by omega
    have hbad : ((i + 1 : ℕ) : ℕ∞) ≤ (i : ℕ∞) := by
      calc
        ((i + 1 : ℕ) : ℕ∞) ≤ ((i + 1 - e + e : ℕ) : ℕ∞) := by exact_mod_cast hnat
        _ = ((i + 1 - e : ℕ) : ℕ∞) + (e : ℕ∞) := by simp
        _ ≤ (⨅ n : ℕ, ⨅ (_ : P n), (n : ℕ∞)) + (e : ℕ∞) :=
          add_le_add hbound le_rfl
        _ ≤ (i : ℕ∞) := hi
    exact (not_le_of_gt
      (show (i : ℕ∞) < ((i + 1 : ℕ) : ℕ∞) by exact_mod_cast Nat.lt_succ_self i)) hbad
  · rintro ⟨n, hn, hni⟩
    calc
      (⨅ n : ℕ, ⨅ (_ : P n), (n : ℕ∞)) + (e : ℕ∞) ≤ (n : ℕ∞) + (e : ℕ∞) :=
        add_le_add (iInf_le_of_le n (iInf_le_of_le hn le_rfl)) le_rfl
      _ ≤ (i : ℕ∞) := by exact_mod_cast hni

/-- Over a Noetherian local ring with normalized dualizing complex, `Ext^j(M, ω)` vanishes in
every positive degree `j`. -/
private theorem ext_subsingleton_of_pos_degree
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (K : DerivedCategory (ModuleCat.{max v u} R)) (M : Type (max v u))
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hK : IsNormalizedDualizingComplex.{u, v} K) (j : ℤ) (hj : 0 < j) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj (ModuleCat.of R M)) K j) := by
  by_cases hM : Nontrivial M
  · let : Nontrivial M := hM
    let E := DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj (ModuleCat.of R M)) K j
    have hdim := supportDim_ext_le_neg_degree.{u, v} K M hK j
    exact (Module.supportDim_eq_bot_iff_subsingleton R E).mp
      (eq_bot_iff.mpr (by simpa [E, not_le_of_gt hj] using hdim))
  · let : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
    let X := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
      (ModuleCat.of R M)
    let hXzero : Limits.IsZero X := Functor.map_isZero _
      (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
    exact ⟨fun x y => hXzero.eq_of_src x y⟩

/-- Shifting the target of an Ext group by `-e` shifts the degree by `e`. -/
private lemma ext_shift_nontrivial_iff
    {R : Type u} [CommRing R]
    (X K : DerivedCategory (ModuleCat.{max v u} R)) (e : ℕ) (j : ℤ) :
    Nontrivial (DerivedCategory.Ext X K j) ↔
      Nontrivial (DerivedCategory.Ext X (K⟦-(e : ℤ)⟧) ((e : ℤ) + j)) := by
  let s := (CategoryTheory.shiftFunctorAdd'
    (DerivedCategory (ModuleCat.{max v u} R)) (-(e : ℤ)) ((e : ℤ) + j) j (by omega)).symm.app K
  change Nontrivial (X ⟶ K⟦j⟧) ↔
    Nontrivial (X ⟶ (K⟦-(e : ℤ)⟧)⟦(e : ℤ) + j⟧)
  exact (CategoryTheory.Iso.homCongr (Iso.refl X) s).nontrivial_congr.symm

/-! ### The support criterion -/

/-- **Stacks Project, Tag 0DWZ, part (4).** Let `(A, 𝔪)` be a Noetherian local ring with a
normalized dualizing complex `ω`, let `M` be a finite `A`-module and write
`Eⁱ = Ext_A^{-i}(M, ω)`. A prime `𝔭` lies in the support of `E⁰ ⊕ E¹ ⊕ ⋯ ⊕ Eⁱ` — realized as
the product over `Fin (i + 1)` — exactly when the depth of the localization `M_𝔭` over `A_𝔭`
plus the dimension of `A / 𝔭` is at most `i`. -/
@[stacks 0DWZ "part (4): p ∈ Supp(E⁰ ⊕ … ⊕ Eⁱ) ↔ depth(M_p) + dim(A/p) ≤ i"]
theorem mem_support_pi_moduleExtInto_iff_depth_add_ringKrullDim_le
    {A : Type u} {M : Type (max v u)}
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{max v u} A))
    (hK : IsNormalizedDualizingComplex.{u, v} K)
    (p : PrimeSpectrum A) (i : ℕ) :
    p ∈ Module.support A ((j : Fin (i + 1)) → moduleExtInto M K (-(j : ℤ))) ↔
      ((Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule p.asIdeal.primeCompl M) : ℕ∞) : WithBot ℕ∞) +
        ringKrullDim (A ⧸ p.asIdeal) ≤ (i : WithBot ℕ∞) := by
  classical
  let T := p.asIdeal.primeCompl
  let R := Localization T
  let G := ModuleCat.localizedModuleFunctor.{max v u} T
  let Mloc := (ModuleCat.of A M).localizedModule T
  let Xloc := (DerivedCategory.singleFunctor (ModuleCat.{max v u} R) 0).obj
    (ModuleCat.of R Mloc)
  let Kloc := G.mapDerivedCategory.obj K
  let eM : Mloc ≃ₗ[R] LocalizedModule T M := Shrink.linearEquiv.{max v u} R _
  let : Module.Finite R (LocalizedModule T M) := inferInstance
  let : Module.Finite R Mloc := Module.Finite.equiv eM.symm
  have hdepthM : Module.depth R (IsLocalRing.maximalIdeal R) Mloc =
      Module.depth R (IsLocalRing.maximalIdeal R) (LocalizedModule T M) :=
    Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal R) eM
  have hKge := exists_isGE_of_isNormalizedDualizingComplex.{u, v} K hK
  have hdimq : ringKrullDim (A ⧸ p.asIdeal) < ⊤ :=
    lt_of_le_of_lt (ringKrullDim_quotient_le p.asIdeal) ringKrullDim_lt_top
  have hdimne : ringKrullDim (A ⧸ p.asIdeal) ≠ ⊥ :=
    fun hbot => (not_subsingleton_iff_nontrivial.mpr
      (Ideal.Quotient.nontrivial_iff.mpr p.isPrime.ne_top))
      ((ringKrullDim_eq_bot_iff_subsingleton (R := A ⧸ p.asIdeal)).mp hbot)
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hdimne
  have hdne : d ≠ ⊤ := by
    intro htop
    exact (ne_of_lt hdimq) (by rw [← hd, htop]; rfl)
  obtain ⟨e, he'⟩ := ENat.ne_top_iff_exists.mp hdne
  have he : ringKrullDim (A ⧸ p.asIdeal) = (e : WithBot ℕ∞) := by
    calc
      ringKrullDim (A ⧸ p.asIdeal) = (d : WithBot ℕ∞) := hd.symm
      _ = (e : WithBot ℕ∞) :=
        congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) he'.symm
  let K' := Kloc⟦-(e : ℤ)⟧
  have hnorm : IsNormalizedDualizingComplex.{u, v} K' := by
    simpa [Kloc, K', G, T] using
      isNormalizedDualizingComplex_localized_shift.{u, v} K hK p.asIdeal e he
  have hloc (j : Fin (i + 1)) :
      Nontrivial (LocalizedModule T (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M))
        K (-(j : ℤ)))) ↔
      Nontrivial (DerivedCategory.Ext Xloc Kloc (-(j : ℤ))) := by
    simpa [T, R, G, Xloc, Mloc] using
      (localized_ext_nontrivial_iff (A := A) (T := T) (M := M)
        K hKge (-(j : ℤ)))
  let E := fun j : Fin (i + 1) =>
    DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).obj (ModuleCat.of A M))
      K (-(j : ℤ))
  have hsupport : p ∈ Module.support A (∀ j : Fin (i + 1), E j) ↔
      ∃ j : Fin (i + 1), Nontrivial (DerivedCategory.Ext Xloc Kloc (-(j : ℤ))) := by
    rw [Module.mem_support_iff]
    change Nontrivial (LocalizedModule T (∀ j : Fin (i + 1), E j)) ↔ _
    rw [(localizedPiEquiv T E).toEquiv.nontrivial_congr.trans
      (nontrivial_pi_iff_exists (M := fun j => LocalizedModule T (E j)))]
    simp only [E, hloc]
  have hbridge :
      (∃ j : Fin (i + 1), Nontrivial (DerivedCategory.Ext Xloc Kloc (-(j : ℤ)))) ↔
        ∃ n : ℕ, Nontrivial (DerivedCategory.Ext Xloc K' (-(n : ℤ))) ∧ n + e ≤ i := by
    constructor
    · rintro ⟨j, hj⟩
      have hshift := (ext_shift_nontrivial_iff Xloc Kloc e (-(j : ℤ))).mp hj
      by_cases hje : e ≤ j.val
      · refine ⟨j.val - e, ?_, by omega⟩
        have hdeg : (e : ℤ) + (-(j.val : ℤ)) = -((j.val - e : ℕ) : ℤ) := by omega
        simpa [Xloc, K', G, ModuleCat.localizedModuleFunctor, hdeg] using hshift
      · have hzero := ext_subsingleton_of_pos_degree K' Mloc hnorm
          ((e : ℤ) + (-(j.val : ℤ))) (by omega)
        exact False.elim ((not_nontrivial_iff_subsingleton.mpr hzero)
          (by simpa [Xloc, K', G, ModuleCat.localizedModuleFunctor] using hshift))
    · rintro ⟨n, hn, hni⟩
      let j : Fin (i + 1) := ⟨e + n, by omega⟩
      refine ⟨j, ?_⟩
      have hdeg : (e : ℤ) + (-(j : ℤ)) = -(n : ℤ) := by simp [j]
      exact (ext_shift_nontrivial_iff Xloc Kloc e (-(j : ℤ))).mpr
        (by simpa [Xloc, G, ModuleCat.localizedModuleFunctor, hdeg] using hn)
  have hdepth := depth_eq_iInf_nontrivial_moduleExtInto.{u, v} (M := Mloc) K' hnorm
  have hdepthCriterion :
      (∃ n : ℕ, Nontrivial (DerivedCategory.Ext Xloc K' (-(n : ℤ))) ∧ n + e ≤ i) ↔
        Module.depth R (IsLocalRing.maximalIdeal R) (LocalizedModule T M) +
          (e : ℕ∞) ≤ (i : ℕ∞) := by
    rw [← hdepthM, hdepth]
    exact (iInf_nat_add_le_iff
      (fun n => Nontrivial (DerivedCategory.Ext Xloc K' (-(n : ℤ)))) e i).symm
  have hdimCriterion :
      Module.depth R (IsLocalRing.maximalIdeal R) (LocalizedModule T M) +
          (e : ℕ∞) ≤ (i : ℕ∞) ↔
        ((Module.depth R (IsLocalRing.maximalIdeal R) (LocalizedModule T M) : ℕ∞) :
          WithBot ℕ∞) + ringKrullDim (A ⧸ p.asIdeal) ≤ (i : WithBot ℕ∞) := by
    rw [he]; norm_cast
  exact hsupport.trans (hbridge.trans (hdepthCriterion.trans hdimCriterion))

end Dualizing

end
