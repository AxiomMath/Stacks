module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Order.Iterate
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.ExtendScalars.Localization
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso
public import StacksFrontier.RingTheory.LocalCohomology.BaseChangeGeneralSupport
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported
public import StacksFrontier.RingTheory.LocalCohomology.EssentiallyConstantSystem
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.LocalizationKernel
public import StacksFrontier.RingTheory.LocalCohomology.ModelComparison.Noetherian
public import StacksFrontier.RingTheory.Spectrum.Prime.NonminimalPrimesDimension

/-!
# Pro-zero local cohomology with support in a specialization-closed set

Let `A` be a Noetherian ring of finite Krull dimension, let `T ⊆ Spec(A)` be stable under
specialization, and let `{M_n}` be an inverse system of `A`-modules. If for every `m` there is
`m'(m) ≥ m` such that the transition map `Hⁱ_{𝔭A_𝔭}(M_{k,𝔭}) → Hⁱ_{𝔭A_𝔭}(M_{m,𝔭})` vanishes for
all `𝔭 ∈ T` and all `k ≥ m'(m)`, then the transition map `Hⁱ_T(M_k) → Hⁱ_T(M_m)` vanishes for
all `k` beyond the `2 ^ dim T`-fold iterate of `m'` at `m`.

## Main definitions

* `Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor` — local cohomology with
  support in `T`, in a fixed degree, applied to a module placed in degree zero.
* `Stacks.LocalCohomology.derivedSupportIsoOfEq` — the identification of derived sections with
  support in two sets with the same underlying elements.

## Main results

* `Stacks.LocalCohomology.localized_support_of_minimal_prime_eq_closedPoint` — at a prime
  minimal in `T`, the preimage of `T` in the spectrum of the localization is the closed point.
* `Stacks.LocalCohomology.localCohomologyWithSupportIn_map_eq_zero_of_local` — the explicit
  vanishing bound for the transition maps of the system of local cohomology modules.

## References

* [Stacks Project, Tag 0EF9](https://stacks.math.columbia.edu/tag/0EF9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u v

namespace Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

open Opposite PrimeSpectrum

/-! ### Iterating the local bound -/

/-- Iterating an inflationary function more times gives a larger value. -/
private theorem iterate_le_iterate_of_le (f : ℕ → ℕ) (hf : ∀ n, n ≤ f n)
    {a b n : ℕ} (hab : a ≤ b) : f^[a] n ≤ f^[b] n := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [Nat.add_comm, Function.iterate_add_apply]
  exact Function.id_le_iterate_of_id_le hf c (f^[a] n)

/-- Two applications of the `2 ^ d`-fold iterate make the `2 ^ (d + 1)`-fold iterate. -/
private theorem iterate_two_pow_iterate_two_pow (f : ℕ → ℕ) (d m : ℕ) :
    f^[2 ^ d] (f^[2 ^ d] m) = f^[2 ^ (d + 1)] m := by
  rw [pow_succ, mul_two, Function.iterate_add_apply]

/-- The transition maps of an inverse system indexed by a preorder compose. -/
private theorem map_comp_map_homOfLE_op
    {A : Type u} [Preorder A] {C : Type v} [Category C]
    (F : Aᵒᵖ ⥤ C) {i j k : A} (hij : i ≤ j) (hjk : j ≤ k) :
    F.map (homOfLE hjk).op ≫ F.map (homOfLE hij).op =
      F.map (homOfLE (hij.trans hjk)).op := by
  rw [← Functor.map_comp]; congr 1

/-! ### Vanishing for the empty support -/

/-- Local cohomology with empty support vanishes. -/
theorem isZero_localCohomologyWithSupportIn_empty
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) :
    IsZero (localCohomologyWithSupportIn.{u, v} A (∅ : Set (PrimeSpectrum A)) K i) :=
  ModuleCat.isZero_iff_subsingleton.mpr <| Module.support_eq_empty_iff.mp <|
    Set.subset_empty_iff.mp
      (support_localCohomologyWithSupportIn_subset.{u, v} (∅ : Set (PrimeSpectrum A)) K i)

/-! ### Local cohomology with support in `T`, on modules -/

/-- Local cohomology with support in `T` in degree `i`, applied to a module placed in degree
zero. -/
def localCohomologyWithSupportInModuleFunctor
    (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) (i : ℤ) :
    ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} A :=
  DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
    derivedSectionsWithSupportIn.{u, v} A T ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i

/-- Local cohomology with support in a set with no elements kills every map of modules. -/
private theorem localCohomologyWithSupportInModuleFunctor_map_eq_zero_of_not_nonempty
    (A : Type u) [CommRing A] [IsNoetherianRing A] (i : ℤ)
    {T : Set (PrimeSpectrum A)} (hT : ¬ T.Nonempty)
    {M N : ModuleCat.{max u v} A} (f : M ⟶ N) :
    (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map f = 0 := by
  obtain rfl := Set.not_nonempty_iff_eq_empty.mp hT
  exact (isZero_localCohomologyWithSupportIn_empty.{u, v} A
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) i).eq_zero_of_tgt _

/-- Changing the support commutes with the map induced by a morphism of derived objects. -/
private theorem changeOfSupport_naturality
    (A : Type u) [CommRing A] {S T : Set (PrimeSpectrum A)} (h : S ⊆ T)
    (K L : DerivedCategory (ModuleCat.{max u v} A)) (i : ℤ) (f : K ⟶ L) :
    changeOfSupport.{u, v} A h K i ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
          ((derivedSectionsWithSupportIn.{u, v} A T).map f) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
          ((derivedSectionsWithSupportIn.{u, v} A S).map f) ≫
        changeOfSupport.{u, v} A h L i := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i
  let η := derivedSectionsWithSupportInInclusion.{u, v} A h
  change H.map (η.app K) ≫ H.map ((derivedSectionsWithSupportIn.{u, v} A T).map f) =
    H.map ((derivedSectionsWithSupportIn.{u, v} A S).map f) ≫ H.map (η.app L)
  rw [← H.map_comp, ← H.map_comp]
  exact (congrArg H.map (η.naturality f)).symm

/-- Changing the support commutes with the map induced by a morphism of modules. -/
theorem changeOfSupportModule_naturality
    (A : Type u) [CommRing A] {S T : Set (PrimeSpectrum A)} (h : S ⊆ T)
    (M N : ModuleCat.{max u v} A) (i : ℤ) (f : M ⟶ N) :
    changeOfSupport.{u, v} A h
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M) i ≫
      (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map f =
    (localCohomologyWithSupportInModuleFunctor.{u, v} A S i).map f ≫
      changeOfSupport.{u, v} A h
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) i := by
  simpa [localCohomologyWithSupportInModuleFunctor, Functor.comp_map] using
    changeOfSupport_naturality.{u, v} A h
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) i
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map f)

/-! ### Localizing at a prime minimal in `T` -/

/-- Restriction of scalars along the localization map at a prime. -/
abbrev restrictScalarsAtPrime (A : Type u) [CommRing A] (p : PrimeSpectrum A) :
    ModuleCat.{max u v} (Localization p.asIdeal.primeCompl) ⥤ ModuleCat.{max u v} A :=
  ModuleCat.restrictScalars.{max u v} (algebraMap A (Localization p.asIdeal.primeCompl))

/-- At a prime of `T` minimal in `T`, the preimage of `T` in the spectrum of the localization is
the closed point. -/
theorem localized_support_of_minimal_prime_eq_closedPoint
    {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A))
    (p : PrimeSpectrum A) (hp : p ∈ T \ nonminimalPrimes T) :
    comap (algebraMap A (Localization p.asIdeal.primeCompl)) ⁻¹' T =
      {IsLocalRing.closedPoint (Localization p.asIdeal.primeCompl)} := by
  let B := Localization p.asIdeal.primeCompl
  let f : A →+* B := algebraMap A B
  have hclosed : comap f (IsLocalRing.closedPoint B) = p :=
    PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
  ext q
  constructor
  · intro hq
    let r : PrimeSpectrum A := comap f q
    have hle : r.asIdeal ≤ p.asIdeal := by
      have hrange : r ∈ Set.range (comap f) := ⟨q, rfl⟩
      rw [PrimeSpectrum.localization_comap_range B p.asIdeal.primeCompl] at hrange
      exact Set.disjoint_compl_left_iff_subset.mp
        (by simpa [Ideal.primeCompl] using hrange)
    have hrT : r ∈ T := hq
    have hrp : r = p := PrimeSpectrum.ext <| le_antisymm hle <| by
      by_contra hpr
      exact hp.2 ⟨hp.1, r, hrT, lt_of_le_not_ge hle hpr⟩
    exact PrimeSpectrum.localization_comap_injective B p.asIdeal.primeCompl
      (hrp.trans hclosed.symm)
  · intro hq
    have hq' : q = IsLocalRing.closedPoint B := hq
    subst hq'
    change comap f (IsLocalRing.closedPoint B) ∈ T
    rw [hclosed]
    exact hp.1

/-- Two supports with the same underlying set have isomorphic derived sections. -/
def derivedSupportIsoOfEq
    (A : Type u) [CommRing A] (S T : Set (PrimeSpectrum A)) (hST : S ⊆ T) (hTS : T ⊆ S) :
    derivedSectionsWithSupportIn.{u, v} A S ≅ derivedSectionsWithSupportIn.{u, v} A T where
  hom := derivedSectionsWithSupportInInclusion.{u, v} A hST
  inv := derivedSectionsWithSupportInInclusion.{u, v} A hTS
  hom_inv_id := by
    rw [derivedSectionsWithSupportInInclusion_trans.{u, v} A hST hTS,
      Subsingleton.elim (hST.trans hTS) (Set.Subset.refl S)]
    exact derivedSectionsWithSupportInInclusion_refl.{u, v} A S
  inv_hom_id := by
    rw [derivedSectionsWithSupportInInclusion_trans.{u, v} A hTS hST,
      Subsingleton.elim (hTS.trans hST) (Set.Subset.refl T)]
    exact derivedSectionsWithSupportInInclusion_refl.{u, v} A T

/-- Derived extension of scalars along the localization map at a prime, applied to a module in
degree zero, is the localized module in degree zero. -/
private def localizedSingleDerivedExtensionIso (A : Type u) [CommRing A] (p : PrimeSpectrum A) :
    DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0 ⋙
        (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
          (algebraMap A (Localization p.asIdeal.primeCompl))).functor ≅
      ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        DerivedCategory.singleFunctor
          (ModuleCat.{max u v} (Localization p.asIdeal.primeCompl)) 0 := by
  let B := Localization p.asIdeal.primeCompl
  let extension := ModuleCat.extendScalars.{u, u, max u v} (algebraMap A B)
  let e := extendScalars_iso_localizedModuleFunctor.{u, v} p.asIdeal.primeCompl
  have : PreservesFiniteLimits extension := preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteColimits extension := preservesFiniteColimits_of_natIso e.symm
  exact Functor.isoWhiskerLeft _
      (derivedExtensionScalarsIsoMapDerivedCategory.{u, v, u} (algebraMap A B)) ≪≫
    extension.mapDerivedCategorySingleFunctor 0 ≪≫ Functor.isoWhiskerRight e _

/-- **Local cohomology with support in `T` localizes to local cohomology at the closed point.**
At a prime `p` minimal in `T`, the localization at `p` of `Hⁱ_T(M)` is `Hⁱ_{pA_p}(M_p)`,
naturally in the `A`-module `M`. -/
@[no_expose] def minimalPrimeLocalCohomologyIso
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (p : PrimeSpectrum A)
    (hp : p ∈ T \ nonminimalPrimes T) (i : ℤ) :
    localCohomologyWithSupportInModuleFunctor.{u, v} A T i ⋙
        CochainComplex.DerivedTensor.localizedModuleFunctor.{u, max u v}
          p.asIdeal.primeCompl ≅
      (ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i) ⋙
          restrictScalarsAtPrime.{u, v} A p := by
  let B := Localization p.asIdeal.primeCompl
  let f := algebraMap A B
  let D := (CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsGeneral.{u, v, u}
    f).functor
  let single := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0
  let H_A := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i
  let H_B := DerivedCategory.homologyFunctor (ModuleCat.{max u v} B) i
  let res := restrictScalarsAtPrime.{u, v} A p
  let support := derivedSectionsWithSupportIn.{u, v} A T
  let m := IsLocalRing.maximalIdeal B
  have hm : m.FG := IsNoetherian.noetherian _
  have hBdim : ringKrullDim B < ⊤ := by
    refine lt_of_le_of_lt ?_ hdim
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B,
      ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A]
    exact (PrimeSpectrum.localization_comap_isInducing B
      p.asIdeal.primeCompl).topologicalKrullDim_le
  have hf : f.Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat B p.asIdeal.primeCompl)
  let eBase := (derivedSectionsWithSupportInBaseChangeIso.{u, v, u} f hf T hT hdim hBdim).val
  have hclosed : PrimeSpectrum.zeroLocus (m : Set B) =
      {IsLocalRing.closedPoint B} := by
    ext q
    change m ≤ q.asIdeal ↔ q = IsLocalRing.closedPoint B
    constructor
    · exact fun hq =>
        PrimeSpectrum.ext (le_antisymm (IsLocalRing.le_maximalIdeal Ideal.IsPrime.ne_top') hq)
    · rintro rfl
      exact le_rfl
  have hpreimage : comap f ⁻¹' T = PrimeSpectrum.zeroLocus (m : Set B) :=
    (localized_support_of_minimal_prime_eq_closedPoint T p hp).trans hclosed.symm
  let eSupport := derivedSupportIsoOfEq.{u, v} B _ _ hpreimage.subset hpreimage.symm.subset
  have hmodel : IsIso (compareSectionsWithSupportLocalCohomology.{u, v} B m hm) :=
    isIso_compareSectionsWithSupportLocalCohomology.{u, v} B m hm
  let eModel := asIso (compareSectionsWithSupportLocalCohomology.{u, v} B m hm)
  let model := Dualizing.localCohomologyFunctor B m hm ⋙
    (Dualizing.derivedPowerTorsionProperty B m hm).ι
  let eLoc : D ⋙ H_B ⋙ res ≅
      H_A ⋙ CochainComplex.DerivedTensor.localizedModuleFunctor p.asIdeal.primeCompl :=
    CochainComplex.DerivedTensor.derivedExtensionScalarsLocalizationHomologyIso.{u, u, v}
      (A := B) p.asIdeal.primeCompl i
  let e₁ : single ⋙ support ⋙ H_A ⋙
        CochainComplex.DerivedTensor.localizedModuleFunctor p.asIdeal.primeCompl ≅
      single ⋙ support ⋙ D ⋙ H_B ⋙ res :=
    Functor.isoWhiskerLeft (single ⋙ support) eLoc.symm
  let e₂ : single ⋙ support ⋙ D ⋙ H_B ⋙ res ≅
      single ⋙ D ⋙ derivedSectionsWithSupportIn.{u, v} B (comap f ⁻¹' T) ⋙ H_B ⋙ res :=
    Functor.isoWhiskerLeft single (Functor.isoWhiskerRight eBase (H_B ⋙ res))
  let e₃ : single ⋙ D ⋙ derivedSectionsWithSupportIn.{u, v} B (comap f ⁻¹' T) ⋙ H_B ⋙ res ≅
      single ⋙ D ⋙ model ⋙ H_B ⋙ res :=
    Functor.isoWhiskerLeft (single ⋙ D)
      (Functor.isoWhiskerRight (eSupport ≪≫ eModel) (H_B ⋙ res))
  let e₄ : single ⋙ D ⋙ model ⋙ H_B ⋙ res ≅
      ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0 ⋙ model ⋙ H_B ⋙ res :=
    Functor.isoWhiskerRight (localizedSingleDerivedExtensionIso.{u, v} A p) (model ⋙ H_B ⋙ res)
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- If the transition map vanishes on local cohomology at a prime `p` minimal in `T`, then every
class in `Hⁱ_T` has image zero in the localization at `p`. -/
private theorem localized_localCohomology_map_eq_zero
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (p : PrimeSpectrum A)
    (hp : p ∈ T \ nonminimalPrimes T) (i : ℤ)
    {M N : ModuleCat.{max u v} A} (f : M ⟶ N)
    (hf : (ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
      localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i).map f = 0)
    (x : (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj M) :
    (ModuleCat.localizedModuleMkLinearMap
      ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj N) p.asIdeal.primeCompl)
        (((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map f).hom x) = 0 := by
  let H := localCohomologyWithSupportInModuleFunctor.{u, v} A T i
  let S := p.asIdeal.primeCompl
  let e := minimalPrimeLocalCohomologyIso.{u, v} A hdim T hT p hp i
  have htarget : ((ModuleCat.localizedModuleFunctor.{max u v} S ⋙
      localCohomologyModuleFunctor (Localization S) i) ⋙
        restrictScalarsAtPrime.{u, v} A p).map f = 0 := by
    rw [Functor.comp_map, hf, Functor.map_zero]
  have hmap : (H ⋙ CochainComplex.DerivedTensor.localizedModuleFunctor S).map f = 0 := by
    have hn := e.hom.naturality f
    rw [htarget, comp_zero] at hn
    exact (cancel_mono (e.hom.app N)).mp (hn.trans zero_comp.symm)
  have hx := congrArg
    (fun g => g.hom (LocalizedModule.mkLinearMap S (H.obj M) x)) hmap
  change IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (H.obj M))
    (LocalizedModule.mkLinearMap S (H.obj N)) (H.map f).hom
      (LocalizedModule.mkLinearMap S (H.obj M) x) = 0 at hx
  rw [IsLocalizedModule.map_apply] at hx
  change (Shrink.linearEquiv A (LocalizedModule S (H.obj N))).symm
    (LocalizedModule.mkLinearMap S (H.obj N) ((H.map f).hom x)) = 0
  rw [hx, map_zero]

/-- **The image of a transition map comes from the nonminimal primes.** If the transition map
vanishes on local cohomology at every prime of `T`, then the image of any class under
`Hⁱ_T(M) → Hⁱ_T(N)` lies in the image of `Hⁱ_{T'}(N)`, where `T'` is the set of nonminimal
primes of `T`. -/
private theorem transition_image_mem_changeOfSupport_range
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (i : ℤ)
    {M N : ModuleCat.{max u v} A} (f : M ⟶ N)
    (hf : ∀ p : PrimeSpectrum A, p ∈ T →
      (ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) i).map f = 0)
    (x : (localCohomologyWithSupportInModuleFunctor.{u, v} A T i).obj M) :
    ∃ y : (localCohomologyWithSupportInModuleFunctor.{u, v} A (nonminimalPrimes T) i).obj N,
      (changeOfSupport.{u, v} A (nonminimalPrimes_subset T)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj N) i).hom y =
          ((localCohomologyWithSupportInModuleFunctor.{u, v} A T i).map f).hom x := by
  exact (range_changeOfSupport_eq_localizationKernel.{u, v} A T hT _ i _).mpr fun p hp =>
    localized_localCohomology_map_eq_zero.{u, v} A hdim T hT p hp i f (hf p hp.1) x

/-! ### The induction on the dimension of the support -/

/-- Vanishing of the transition maps for local cohomology with support in `T`, given a bound `n`
for the length of the longest descending chain of primes of `T`: the `2 ^ n`-fold iterate of `m'`
suffices. -/
theorem localCohomologyWithSupportIn_map_eq_zero_of_local_of_dimension_le
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤)
    (F : ℕᵒᵖ ⥤ ModuleCat.{max u v} A) (i : ℕ)
    (m' : ℕ → ℕ) (hm' : ∀ m, m ≤ m' m) (n : ℕ)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (hTdim : nonminimalDim T ≤ n)
    (hlocal : ∀ (m k : ℕ) (hbound : m' m ≤ k),
      ∀ (p : PrimeSpectrum A), p ∈ T →
      ((ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
        (F.map (homOfLE ((hm' m).trans hbound)).op) = 0))
    (m k : ℕ) (hk : m'^[2 ^ n] m ≤ k) :
    (localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
      (F.map (homOfLE
        ((Function.id_le_iterate_of_id_le hm' _ m).trans hk)).op) = 0 := by
  induction n generalizing T m k with
  | zero =>
    by_cases hTne : T.Nonempty
    · have hempty : nonminimalPrimes T = ∅ := by
        by_contra hne
        have hlt := nonminimalDim_nonminimalPrimes_lt T hTne
          (Set.nonempty_iff_ne_empty.mpr hne) hdim
        omega
      apply ModuleCat.hom_ext
      ext x
      have hbound : m' m ≤ k := by simpa using hk
      obtain ⟨y, hy⟩ := transition_image_mem_changeOfSupport_range.{u, v} A hdim T hT
        (i : ℤ) (F.map (homOfLE ((hm' m).trans hbound)).op) (hlocal m k hbound) x
      have hsrc : IsZero ((localCohomologyWithSupportInModuleFunctor.{u, v} A
          (nonminimalPrimes T) (i : ℤ)).obj (F.obj (op m))) := by
        rw [hempty]
        exact isZero_localCohomologyWithSupportIn_empty.{u, v} A _ (i : ℤ)
      have hy0 : y = 0 :=
        @Subsingleton.elim _ (ModuleCat.isZero_iff_subsingleton.mp hsrc) y 0
      change ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
        (F.map (homOfLE ((hm' m).trans hbound)).op)).hom x = 0
      rw [← hy, hy0]
      exact map_zero _
    · exact localCohomologyWithSupportInModuleFunctor_map_eq_zero_of_not_nonempty.{u, v}
        A (i : ℤ) hTne _
  | succ n ih =>
    by_cases hTne : T.Nonempty
    · let T' := nonminimalPrimes T
      have hT'stable := stableUnderSpecialization_nonminimalPrimes hT
      let q := m'^[2 ^ n] m
      have hmq : m ≤ q := Function.id_le_iterate_of_id_le hm' _ m
      have hqk : m'^[2 ^ n] q ≤ k := by
        simpa only [q, iterate_two_pow_iterate_two_pow] using hk
      have hlocalbound : m' q ≤ k :=
        (iterate_le_iterate_of_le m' hm' (Nat.one_le_pow n 2 (by omega))).trans hqk
      have hqkle : q ≤ k := (hm' q).trans hlocalbound
      have hleft : (localCohomologyWithSupportInModuleFunctor.{u, v} A T' (i : ℤ)).map
          (F.map (homOfLE hmq).op) = 0 := by
        by_cases hT'ne : T'.Nonempty
        · have hT'dim : nonminimalDim T' ≤ n := by
            have hlt := nonminimalDim_nonminimalPrimes_lt T hTne hT'ne hdim
            change nonminimalDim T' < nonminimalDim T at hlt
            omega
          exact ih T' hT'stable hT'dim
            (fun m k hbound p hp => hlocal m k hbound p hp.1) m q le_rfl
        · exact localCohomologyWithSupportInModuleFunctor_map_eq_zero_of_not_nonempty.{u, v}
            A (i : ℤ) hT'ne _
      apply ModuleCat.hom_ext
      ext x
      obtain ⟨y, hy⟩ := transition_image_mem_changeOfSupport_range.{u, v} A hdim T hT
        (i : ℤ) (F.map (homOfLE hqkle).op) (hlocal q k hlocalbound) x
      have hleft_y : ((localCohomologyWithSupportInModuleFunctor.{u, v} A T' (i : ℤ)).map
          (F.map (homOfLE hmq).op)).hom y = 0 := by
        simpa using congrArg (fun φ => φ.hom y) hleft
      have hcomm := congrArg (fun φ => φ.hom y)
        (changeOfSupportModule_naturality.{u, v} A (S := T') (T := T)
          (nonminimalPrimes_subset T) (F.obj (op q)) (F.obj (op m)) (i : ℤ)
          (F.map (homOfLE hmq).op))
      change ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
          (F.map (homOfLE hmq).op)).hom
          ((changeOfSupport.{u, v} A (nonminimalPrimes_subset T)
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
              (F.obj (op q))) (i : ℤ)).hom y) =
        (changeOfSupport.{u, v} A (nonminimalPrimes_subset T)
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
            (F.obj (op m))) (i : ℤ)).hom
          (((localCohomologyWithSupportInModuleFunctor.{u, v} A T' (i : ℤ)).map
            (F.map (homOfLE hmq).op)).hom y) at hcomm
      rw [← map_comp_map_homOfLE_op F hmq hqkle, Functor.map_comp]
      change ((localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
        (F.map (homOfLE hmq).op)).hom
        (((localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
          (F.map (homOfLE hqkle).op)).hom x) = 0
      rw [← hy, hcomm, hleft_y]
      exact map_zero _
    · exact localCohomologyWithSupportInModuleFunctor_map_eq_zero_of_not_nonempty.{u, v}
        A (i : ℤ) hTne _

/-- Let `A` be a Noetherian ring of finite Krull dimension, let `T ⊆ Spec(A)` be stable under
specialization and let `{M_n}` be an inverse system of `A`-modules. If for every `m` the
transition maps `Hⁱ_{pA_p}(M_{k,p}) → Hⁱ_{pA_p}(M_{m,p})` vanish for all `p ∈ T` and all
`k ≥ m'(m)`, then `Hⁱ_T(M_k) → Hⁱ_T(M_m)` vanishes for all `k` beyond the `2 ^ dim T`-fold
iterate of `m'` at `m`. -/
@[stacks 0EF9]
theorem localCohomologyWithSupportIn_map_eq_zero_of_local
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hdim : ringKrullDim A < ⊤)
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (F : ℕᵒᵖ ⥤ ModuleCat.{max u v} A) (i : ℕ)
    (m' : ℕ → ℕ) (hm' : ∀ m, m ≤ m' m)
    (hlocal : ∀ (m k : ℕ) (hbound : m' m ≤ k),
      ∀ (p : PrimeSpectrum A), p ∈ T →
      ((ModuleCat.localizedModuleFunctor.{max u v} p.asIdeal.primeCompl ⋙
        localCohomologyModuleFunctor (Localization p.asIdeal.primeCompl) (i : ℤ)).map
        (F.map (homOfLE ((hm' m).trans hbound)).op) = 0))
    (m k : ℕ)
    (hk : m'^[2 ^ ((topologicalKrullDim (↥T)).unbotD 0).toNat] m ≤ k) :
    (localCohomologyWithSupportInModuleFunctor.{u, v} A T (i : ℤ)).map
      (F.map (homOfLE
        ((Function.id_le_iterate_of_id_le (fun m => hm' m) _ m).trans hk)).op) = 0 := by
  by_cases hTne : T.Nonempty
  · exact localCohomologyWithSupportIn_map_eq_zero_of_local_of_dimension_le.{u, v}
      A hdim F i m' hm' _ T hT (nonminimalDim_le_topologicalDim T hTne hdim) hlocal m k hk
  · exact localCohomologyWithSupportInModuleFunctor_map_eq_zero_of_not_nonempty.{u, v}
      A (i : ℤ) hTne _

end Stacks.LocalCohomology

end
