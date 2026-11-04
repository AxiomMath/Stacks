module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.RingTheory.Localization.Module
public import StacksFrontier.RingTheory.Depth.UnqualifiedDepth
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Order.HeightCoheight
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Depth.ShortExact
public import StacksFrontier.RingTheory.Dualizing.CanonicalModule
public import StacksFrontier.RingTheory.Dualizing.ExtDegreeBounds
public import StacksFrontier.RingTheory.Dualizing.MaximalIdealPowerTorsion
public import StacksFrontier.RingTheory.Dualizing.NormalizedFiniteLengthQuotient
public import StacksFrontier.RingTheory.Dualizing.NormalizedRegularQuotient
public import StacksFrontier.RingTheory.Serre.Defs
public import StacksFrontier.RingTheory.Support.Finite
public import StacksFrontier.Topology.Dimension.Krull

import StacksFrontier.RingTheory.Dualizing.Depth

/-!
# Depth of the canonical module

Let `A` be a Noetherian local ring with a normalized dualizing complex `ω_A^•`, let `d = dim(A)`
and let `ω_A = H^{-d}(ω_A^•)` be its canonical module. Then `depth(ω_A) ≥ min(d, 2)`, and
consequently `ω_A` satisfies Serre's condition `(S₂)`.

## Main results

* `Dualizing.min_two_le_depth_canonicalModule`: `depth(ω_A) ≥ min(dim A, 2)`.
* `Dualizing.propertySkModule_canonicalModule`: Stacks 0AWE, part (2).

## References

* [Stacks Project, Tag 0AWE](https://stacks.math.columbia.edu/tag/0AWE)
* [Stacks Project, Tag 0A7S](https://stacks.math.columbia.edu/tag/0A7S)
* [Stacks Project, Tag 0A7T](https://stacks.math.columbia.edu/tag/0A7T)
* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits
open scoped Pointwise

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-! ### Depth and support dimension bookkeeping -/

private lemma smul_top_ne_top_of_finite
    {R X : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup X] [Module R X] [Module.Finite R X] [Nontrivial X] :
    IsLocalRing.maximalIdeal R • (⊤ : Submodule R X) ≠ ⊤ := by
  intro h
  have hz : (⊤ : Submodule R X) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top h.ge
      (by simpa using (IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).ge)
  exact top_ne_bot hz

private lemma depth_eq_of_linearEquiv
    {R : Type*} [CommRing R] {J : Ideal R}
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    Module.depth R J M = Module.depth R J N := by
  have hset : {rs : List R | (∀ r ∈ rs, r ∈ J) ∧ RingTheory.Sequence.IsRegular M rs}
      = {rs : List R | (∀ r ∈ rs, r ∈ J) ∧ RingTheory.Sequence.IsRegular N rs} := by
    ext rs
    simp only [Set.mem_ofPred_eq, e.isRegular_congr rs]
  have htop : J • (⊤ : Submodule R M) = ⊤ ↔ J • (⊤ : Submodule R N) = ⊤ := by
    rw [← Submodule.map_eq_top_iff (e := e), Submodule.map_smul'', Submodule.map_top,
      LinearEquiv.range]
  simp only [Module.depth, hset, htop]

private lemma moduleSupportDim_eq_supportDim
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] : moduleSupportDim R M = Module.supportDim R M := by
  unfold moduleSupportDim
  rw [Module.support_eq_zeroLocus, topologicalKrullDim_zeroLocus]
  exact (Module.supportDim_eq_ringKrullDim_quotient_annihilator R M).symm

private lemma ringKrullDim_eq_natCast_toNat
    {R : Type u} [CommRing R] (hbot : ringKrullDim R ≠ ⊥) (htop : ringKrullDim R ≠ ⊤) :
    ringKrullDim R = ((((ringKrullDim R).unbotD 0).toNat : ℕ) : WithBot ℕ∞) := by
  cases hd : ringKrullDim R with
  | bot => exact (hbot hd).elim
  | coe x =>
    have hx : x ≠ ⊤ := fun hx ↦ htop (by simp [hd, hx])
    simp only [WithBot.unbotD_coe]
    exact_mod_cast (ENat.natCast_toNat hx).symm

private lemma quotient_add_localization_dim_le
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] :
    ringKrullDim (A ⧸ p) + ringKrullDim (Localization.AtPrime p) ≤ ringKrullDim A := by
  rw [← coheight_eq_ringKrullDim_quotient (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum A),
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    PrimeSpectrum.height_eq_orderHeight ⟨p, ‹p.IsPrime›⟩]
  change _ ≤ Order.krullDim (PrimeSpectrum A)
  simpa [add_comm] using
    Order.height_add_coheight_le_krullDim (⟨p, ‹p.IsPrime›⟩ : PrimeSpectrum A)

private lemma propertySkModule_atPrime_of_subsingleton
    {B : Type u} [CommRing B] [IsNoetherianRing B]
    (M : Type u) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (p : Ideal B) [p.IsPrime] (hM : Subsingleton (LocalizedModule.AtPrime p M)) :
    min (2 : ℕ∞)
        ((moduleSupportDim (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).unbotD 0) ≤
      moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p M) := by
  classical
  have hdepth : moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p M) = 0 := by
    refine le_antisymm ?_ bot_le
    unfold moduleDepth
    refine iSup_le fun xs => iSup_le fun hxs => ?_
    have hsub' : Subsingleton
        (Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) :=
      (Submodule.subsingleton_iff _).mpr hM
    exact absurd (Subsingleton.elim (⊤ : Submodule (Localization.AtPrime p)
      (LocalizedModule.AtPrime p M)) (Ideal.ofList xs • ⊤)) hxs.2.top_ne_smul
  have hsupp : Module.support (Localization.AtPrime p) (LocalizedModule.AtPrime p M) = ∅ :=
    Module.support_eq_empty_iff.mpr hM
  have hsupportDim :
      moduleSupportDim (Localization.AtPrime p) (LocalizedModule.AtPrime p M) = ⊥ := by
    unfold moduleSupportDim
    rw [topologicalKrullDim_eq_bot_iff_isEmpty]
    exact Set.isEmpty_coe_sort.mpr hsupp
  rw [hsupportDim, hdepth]
  simp

private lemma depth_eq_of_surjective_algebra
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type*} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (hsurj : Function.Surjective (algebraMap A B)) (J : Ideal A) :
    Module.depth A J M = Module.depth B (J.map (algebraMap A B)) M := by
  have hreg : ∀ rs : List A, RingTheory.Sequence.IsRegular M rs ↔
      RingTheory.Sequence.IsRegular M (rs.map (algebraMap A B)) := fun rs =>
    (AddEquiv.refl M).isRegular_congr <| List.forall₂_map_right_iff.mpr <|
      List.forall₂_same.mpr fun r _ x => (algebraMap_smul B r x).symm
  have htop : J • (⊤ : Submodule A M) = ⊤ ↔
      (J.map (algebraMap A B)) • (⊤ : Submodule B M) = ⊤ := by
    rw [← Submodule.restrictScalars_eq_top_iff (S := A)
      (p := (J.map (algebraMap A B)) • (⊤ : Submodule B M)), Ideal.smul_restrictScalars,
      Submodule.restrictScalars_top]
  have hlift : ∀ ss : List B, (∀ s ∈ ss, s ∈ J.map (algebraMap A B)) →
      ∃ rs : List A, (∀ r ∈ rs, r ∈ J) ∧ rs.map (algebraMap A B) = ss := by
    intro ss
    induction ss with
    | nil => exact fun _ => ⟨[], by simp, rfl⟩
    | cons s ss ih =>
      intro hmem
      obtain ⟨rs, hrs, hmap⟩ := ih fun t ht => hmem t (List.mem_cons_of_mem _ ht)
      obtain ⟨a, ha, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp
        (hmem s List.mem_cons_self)
      exact ⟨a :: rs, by simpa using ⟨ha, hrs⟩, by simp [hmap]⟩
  simp only [Module.depth, htop]
  refine if_congr Iff.rfl rfl (le_antisymm ?_ ?_)
  · refine iSup₂_le fun rs hrs => le_iSup₂_of_le (rs.map (algebraMap A B)) ?_ ?_
    · exact ⟨fun s hs => by
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
        exact Ideal.mem_map_of_mem _ (hrs.1 r hr), (hreg rs).mp hrs.2⟩
    · simp
  · refine iSup₂_le fun ss hss => ?_
    obtain ⟨rs, hrs, rfl⟩ := hlift ss hss.1
    refine le_iSup₂_of_le rs ⟨fun r hr => hrs r hr, (hreg rs).mpr hss.2⟩ ?_
    simp

private lemma depth_maximalIdeal_eq_of_surjective_algebra
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] {M : Type*} [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Module.depth A (IsLocalRing.maximalIdeal A) M =
      Module.depth B (IsLocalRing.maximalIdeal B) M := by
  rw [depth_eq_of_surjective_algebra hsurj (IsLocalRing.maximalIdeal A),
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj]

/-- The quotient of a local ring by an ideal inside the maximal ideal is local. -/
private lemma isLocalRing_quotient_of_le_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] {I : Ideal A} (h : I ≤ IsLocalRing.maximalIdeal A) :
    IsLocalRing (A ⧸ I) :=
  have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (lt_of_le_of_lt h (IsLocalRing.maximalIdeal.isMaximal A).lt_top).ne
  .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

/-! ### Regular elements and depth -/

private lemma exists_mem_maximalIdeal_isSMulRegular_of_depth_pos
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : 0 < Module.depth R (IsLocalRing.maximalIdeal R) M) :
    ∃ x ∈ IsLocalRing.maximalIdeal R, IsSMulRegular M x := by
  classical
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact ⟨0, Ideal.zero_mem _, fun x y _ => hM.elim _ _⟩
  · have : Nontrivial M := hM
    obtain ⟨rs, hrs, hreg, hlen⟩ :=
      (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append
        (IsLocalRing.maximalIdeal R) M).2 smul_top_ne_top_of_finite [] (by simp)
        (RingTheory.Sequence.IsRegular.nil R M)
    cases rs with
    | nil =>
        simp at hlen
        simp [hlen] at h
    | cons x xs =>
        exact ⟨x, hrs x (by simp),
          (RingTheory.Sequence.isRegular_cons_iff M x xs).mp hreg |>.1⟩

private lemma one_le_depth_of_smulRegular
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) {x : R} (hx : x ∈ I) (hreg : IsSMulRegular M x) :
    1 ≤ Module.depth R I M := by
  have heq := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I M).1 x hx hreg
  rw [← heq]
  exact le_add_self

private lemma two_le_depth_of_smulRegular
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) {x : R} (hx : x ∈ I) (hreg : IsSMulRegular M x)
    (hquot : 1 ≤ Module.depth R I (QuotSMulTop x M)) :
    2 ≤ Module.depth R I M := by
  have heq := (Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append I M).1 x hx hreg
  rw [← heq, ← one_add_one_eq_two]
  gcongr

private lemma two_le_depth_of_smulRegular_of_quotient_embeds
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R) (hregM : IsSMulRegular M x)
    (f : QuotSMulTop x M →ₗ[R] N) (hf : Function.Injective f)
    (hN : 0 < Module.depth R (IsLocalRing.maximalIdeal R) N) :
    2 ≤ Module.depth R (IsLocalRing.maximalIdeal R) M := by
  obtain ⟨y, hy, hregN⟩ := exists_mem_maximalIdeal_isSMulRegular_of_depth_pos hN
  have hregQ : IsSMulRegular (QuotSMulTop x M) y := fun a b hab ↦
    hf (hregN (by simpa using congrArg f hab))
  exact two_le_depth_of_smulRegular _ hx hregM (one_le_depth_of_smulRegular _ hy hregQ)

/-! ### Reading the long exact cohomology sequence of a triangle -/

private lemma mono_homology_map_second_of_isZero_first
    {A : Type u} [CommRing A]
    (T : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} A))) (i : ℤ)
    (h₁ : IsZero (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i).obj T.obj₁)) :
    Mono (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i).map T.mor₂) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequence_exact₂
    T hT i).mono_g_iff.mpr (h₁.eq_of_src _ _)

private lemma isSMulRegular_of_mono_homology_smul_id
    {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) {x : A}
    [Functor.Linear A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i)]
    (hmono : Mono (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i).map
      (x • 𝟙 K))) :
    IsSMulRegular (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i).obj K) x := by
  let H := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i
  have hmap : H.map (x • 𝟙 K) = x • 𝟙 (H.obj K) := by
    rw [Functor.Linear.map_smul, H.map_id]
  have hinj : Function.Injective ((x • 𝟙 (H.obj K)).hom) :=
    (ModuleCat.mono_iff_injective _).mp (hmap ▸ hmono)
  exact fun _ _ hab ↦ hinj hab

private lemma isIso_homology_map_mor₁_of_isZero_third
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang (DerivedCategory C)) (i : ℤ)
    (h₀ : IsZero ((DerivedCategory.homologyFunctor C (i - 1)).obj T.obj₃))
    (h₁ : IsZero ((DerivedCategory.homologyFunctor C i).obj T.obj₃)) :
    IsIso ((DerivedCategory.homologyFunctor C i).map T.mor₁) := by
  have hmono : Mono ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).mpr
      (h₀.eq_zero_of_src _)
  have hepi : Epi ((DerivedCategory.homologyFunctor C i).map T.mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mpr
      (h₁.eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

private lemma injective_liftQ_of_exact
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : Function.Exact f g) :
    Function.Injective ((LinearMap.range f).liftQ g
      (le_of_eq (LinearMap.exact_iff.mp h).symm)) := by
  have hrange : LinearMap.ker g = LinearMap.range f := LinearMap.exact_iff.mp h
  exact LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot (LinearMap.range f) g (le_of_eq hrange.symm) (le_of_eq hrange))

private noncomputable def homologySequenceQuotientMap
    {A : Type u} [CommRing A]
    (T : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} A))) (i : ℤ) :
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i).obj T.obj₃) ⧸
      LinearMap.range
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i).map T.mor₂).hom →ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i + 1)).obj T.obj₁) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0
  let f := (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i).map T.mor₂).hom
  let g := (H.homologySequenceδ T i (i + 1) rfl).hom
  have hexFun : Function.Exact f g :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (H.homologySequence_exact₃ T hT i (i + 1) rfl)
  exact (LinearMap.range f).liftQ g (le_of_eq (LinearMap.exact_iff.mp hexFun).symm)

private lemma homologySequenceQuotientMap_injective
    {A : Type u} [CommRing A]
    (T : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} A))) (i : ℤ) :
    Function.Injective (homologySequenceQuotientMap T hT i) :=
  injective_liftQ_of_exact _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).homologySequence_exact₃ T hT i (i + 1)
      rfl))

private noncomputable def homologySequenceSMulQuotientMap
    {A : Type u} [CommRing A]
    (T : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} A))) (i : ℤ)
    [Functor.Linear A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i)]
    {x : A} (hObj : T.obj₂ = T.obj₃) (hmor : T.mor₂ = x • eqToHom hObj) :
    QuotSMulTop x (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i).obj
      T.obj₃) →ₗ[A]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i + 1)).obj T.obj₁) := by
  let F := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i
  let M₃ := F.obj T.obj₃
  let e : F.obj T.obj₂ ≃ₗ[A] M₃ := (F.mapIso (eqToIso hObj)).toLinearEquiv
  let f := (F.map T.mor₂).hom
  have hf : f = x • e.toLinearMap := by
    dsimp [f]
    rw [hmor, Functor.Linear.map_smul]
    rfl
  have hrange : LinearMap.range f = x • (⊤ : Submodule A M₃) := by
    rw [hf]
    ext y
    simp only [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨e z, by simp, hz⟩
    · rintro ⟨z, hz⟩
      obtain ⟨w, rfl⟩ := e.surjective z
      exact ⟨w, hz.2⟩
  have hp : Submodule.map (LinearEquiv.refl A M₃).toLinearMap (x • (⊤ : Submodule A M₃)) =
      LinearMap.range f := by
    rw [Submodule.map_pointwise_smul, LinearEquiv.refl_toLinearMap, Submodule.map_id]
    exact hrange.symm
  exact (homologySequenceQuotientMap T hT i).comp
    (Submodule.Quotient.equiv (x • (⊤ : Submodule A M₃)) (LinearMap.range f)
      (LinearEquiv.refl A M₃) hp).toLinearMap

private lemma homologySequenceSMulQuotientMap_injective
    {A : Type u} [CommRing A]
    (T : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} A))) (i : ℤ)
    [Functor.Linear A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift i)]
    {x : A} (hObj : T.obj₂ = T.obj₃) (hmor : T.mor₂ = x • eqToHom hObj) :
    Function.Injective (homologySequenceSMulQuotientMap T hT i hObj hmor) :=
  (homologySequenceQuotientMap_injective T hT i).comp (Submodule.Quotient.equiv _ _ _ _).injective

/-! ### The depth bound -/

private lemma min_two_le_depth_of_depth_pos
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (d : ℕ) (hdpos : 0 < d) (hd : ringKrullDim A = (d : WithBot ℕ∞))
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, u} K)
    (ih : ∀ (n : ℕ), n < d →
      ∀ {B : Type u} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
        (L : DerivedCategory (ModuleCat.{u} B))
        (_ : IsNormalizedDualizingComplex.{u, u} L)
        (_ : ringKrullDim B = (n : WithBot ℕ∞)),
        min (n : ℕ∞) 2 ≤ Module.depth B (IsLocalRing.maximalIdeal B)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-(n : ℤ))).obj L))
    (hdepth : 0 < Module.depth A (IsLocalRing.maximalIdeal A) A) :
    min (d : ℕ∞) 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K) := by
  let ω := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K
  have : Module.Finite A ω := hK.1.finiteCohomology (-(d : ℤ))
  obtain ⟨f, hf, hregA⟩ := exists_mem_maximalIdeal_isSMulRegular_of_depth_pos hdepth
  have hfnd : f ∈ nonZeroDivisors A := by
    rw [← isRegular_iff_mem_nonZeroDivisors]
    exact ⟨hregA, fun x y hxy => hregA (by simpa [mul_comm] using hxy)⟩
  let B := A ⧸ Ideal.span {f}
  let q : A →+* B := Ideal.Quotient.mk (Ideal.span {f})
  have : IsLocalRing B := isLocalRing_quotient_of_le_maximalIdeal
    (Ideal.span_le.2 (Set.singleton_subset_iff.mpr hf))
  have : IsNoetherianRing B := inferInstance
  have hfB := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
    hfnd hf
  have hdB : ringKrullDim B = ((d - 1 : ℕ) : WithBot ℕ∞) := by
    have hh := hfB.trans hd
    cases hB : ringKrullDim B with
    | bot => rw [hB] at hh; simp at hh
    | coe n =>
      cases hn' : n with
      | top =>
        rw [hB, hn'] at hh
        have htop : (⊤ : ℕ∞) + 1 = (d : ℕ∞) := WithBot.coe_injective hh
        simp only [top_add] at htop
        exact absurd htop (ENat.top_ne_natCast d)
      | coe m =>
        rw [hB, hn'] at hh
        have hn : m + 1 = d := by exact_mod_cast hh
        change (m : WithBot ℕ∞) = ((d - 1 : ℕ) : WithBot ℕ∞)
        exact congrArg (fun x : ℕ => (x : WithBot ℕ∞)) (by omega : d - 1 = m).symm
  have hdlt : d - 1 < d := by omega
  obtain ⟨KB, hKB, i, δ, hT⟩ :=
    exists_distinguishedTriangle_quotient_nonZeroDivisor.{u, u} K hK f hf hfnd
  let T := Triangle.mk i (f • 𝟙 K) δ
  let F := ModuleCat.restrictScalars q
  let e0 := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    F (-(d : ℤ))).app KB
  have hzeroA : IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj T.obj₁) := by
    have hzB : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-(d : ℤ))).obj KB) :=
      isZero_homology_of_lt_neg_ringKrullDim KB hKB (d - 1) hdB (-(d : ℤ)) (by omega)
    exact e0.isZero_iff.mpr (F.map_isZero hzB)
  have hlin : Functor.Linear A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shift (-(d : ℤ))) := by
    rw [DerivedCategory.shift_homologyFunctor]
    exact DerivedCategory.homologyFunctor_linear (C := ModuleCat.{u} A) A (-(d : ℤ))
  have hmono := mono_homology_map_second_of_isZero_first T hT (-(d : ℤ)) hzeroA
  have hregω : IsSMulRegular ω f := by
    apply isSMulRegular_of_mono_homology_smul_id K (-(d : ℤ))
    simpa [T] using hmono
  by_cases hd1 : d = 1
  · subst d
    simp only [Nat.cast_one, min_eq_left (by norm_num : (1 : ℕ∞) ≤ 2)]
    exact one_le_depth_of_smulRegular _ hf hregω
  · have hd2 : 2 ≤ d := by omega
    have hmor : T.mor₂ = f • eqToHom (show T.obj₂ = T.obj₃ by rfl) := by simp [T]
    let seqMap := homologySequenceSMulQuotientMap T hT (-(d : ℤ))
      (show T.obj₂ = T.obj₃ by rfl) hmor
    have hseqInjective := homologySequenceSMulQuotientMap_injective T hT
      (-(d : ℤ)) (show T.obj₂ = T.obj₃ by rfl) hmor
    let N := (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-((d - 1 : ℕ) : ℤ))).obj KB
    let : Module A N := Module.compHom N (algebraMap A B)
    have : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    have : Module.Finite B N := hKB.1.finiteCohomology (-((d - 1 : ℕ) : ℤ))
    have : Module.Finite A B := Module.Finite.of_surjective
      (Algebra.linearMap A B) Ideal.Quotient.mk_surjective
    have : Module.Finite A N := Module.Finite.trans B N
    have hdepthN_B := ih (d - 1) hdlt KB hKB hdB
    have hdepthN_B_pos : 0 < Module.depth B (IsLocalRing.maximalIdeal B) N := by
      have hmin : (1 : ℕ∞) ≤ min ((d - 1 : ℕ) : ℕ∞) 2 :=
        le_min (by exact_mod_cast (by omega : 1 ≤ d - 1)) (by norm_num)
      exact lt_of_lt_of_le (by norm_num) (hmin.trans hdepthN_B)
    have hdepthN_A : 0 < Module.depth A (IsLocalRing.maximalIdeal A) N :=
      (depth_maximalIdeal_eq_of_surjective_algebra (A := A) (B := B) (M := N)
        Ideal.Quotient.mk_surjective).symm ▸
        hdepthN_B_pos
    have hdeg : -(d : ℤ) + 1 = -((d - 1 : ℕ) : ℤ) := by omega
    let e := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      F (-((d - 1 : ℕ) : ℤ))).app KB
    let e' : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ) + 1)).obj T.obj₁) ≃ₗ[A]
        (F.obj (ModuleCat.of B N)) := by
      rw [hdeg]
      exact e.toLinearEquiv
    let emb : QuotSMulTop f ω →ₗ[A] N := e'.toLinearMap.comp seqMap
    have hemb : Function.Injective emb := e'.injective.comp hseqInjective
    exact (min_le_right _ _).trans
      (two_le_depth_of_smulRegular_of_quotient_embeds hf hregω emb hemb hdepthN_A)

/-- For a Noetherian local ring `A` with a normalized dualizing complex `K` and `d = dim(A)`, the
canonical module `H^{-d}(K)` has depth at least `min(d, 2)`. -/
theorem min_two_le_depth_canonicalModule :
    ∀ (d : ℕ) {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (K : DerivedCategory (ModuleCat.{u} A))
      (_ : IsNormalizedDualizingComplex.{u, u} K)
      (_ : ringKrullDim A = (d : WithBot ℕ∞)),
      min (d : ℕ∞) 2 ≤ Module.depth A (IsLocalRing.maximalIdeal A)
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro A instC instN instL K hK hd
    let ω := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K
    have : Module.Finite A ω := hK.1.finiteCohomology (-(d : ℤ))
    by_cases hd0 : d = 0
    · subst d; simp
    by_cases hdepth : 0 < Module.depth A (IsLocalRing.maximalIdeal A) A
    · exact min_two_le_depth_of_depth_pos d (by omega) hd K hK ih hdepth
    · let I : Ideal A := maximalIdealPowerTorsion (A := A) A
      have hIfl : IsFiniteLength A I := isFiniteLength_maximalIdealPowerTorsion A A
      have hIle : I ≤ IsLocalRing.maximalIdeal A := by
        intro a ha
        by_contra ham
        have hau : IsUnit a := IsLocalRing.notMem_maximalIdeal.mp ham
        obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem A (IsLocalRing.maximalIdeal A) a).mp ha
        have hkill : ∀ b : ↥((IsLocalRing.maximalIdeal A) ^ n), (b : A) * a = 0 := by
          intro b
          simpa [smul_eq_mul] using (Submodule.mem_torsionBySet_iff _ _).mp hn b
        have hpow : (IsLocalRing.maximalIdeal A) ^ n = ⊥ := by
          refine bot_unique fun b hb => ?_
          have hz : b * a = 0 * a := by simpa using hkill ⟨b, hb⟩
          exact (IsUnit.mul_left_inj hau).mp hz
        have hdim0 : Ring.KrullDimLE 0 A := by
          refine Ring.krullDimLE_zero_iff.mpr fun p hp => ?_
          have hmp : IsLocalRing.maximalIdeal A ≤ p :=
            Ideal.IsPrime.le_of_pow_le (by rw [hpow]; exact bot_le)
          rw [le_antisymm (IsLocalRing.le_maximalIdeal hp.ne_top) hmp]
          exact IsLocalRing.maximalIdeal.isMaximal A
        have hle0 : ringKrullDim A ≤ 0 := Ring.krullDimLE_iff.mp hdim0
        rw [hd] at hle0
        have hdle : d ≤ 0 := by exact_mod_cast hle0
        omega
      let B := A ⧸ I
      let q : A →+* B := Ideal.Quotient.mk I
      have : IsLocalRing B := isLocalRing_quotient_of_le_maximalIdeal hIle
      have : IsNoetherianRing B := inferInstance
      obtain ⟨E, i, hiMono, hiHull⟩ := Module.exists_isInjectiveHull.{u, u} A
        ((ModuleCat.uliftFunctor.{u} A).obj (ModuleCat.of A (IsLocalRing.ResidueField A)))
      let i' : (ModuleCat.uliftFunctor.{u} A).obj
          (ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A)) ⟶ E := i
      have : Mono i' := hiMono
      have hiHull' : Module.IsInjectiveHull i' := hiHull
      obtain ⟨KB, hKB, f₀, g, δ, hT⟩ :=
        exists_distTriang_normalizedDualizing_quotient_finiteLengthIdeal.{u, u}
          K hK I hIle hIfl E i' hiHull'
      let T := Triangle.mk f₀ g δ
      have hdimApos : 0 < Module.supportDim A A := by
        rw [Module.supportDim_self_eq_ringKrullDim, hd]
        exact_mod_cast (show 0 < d by omega)
      have hdimQ := supportDim_quotientMaximalIdealPowerTorsion A A hdimApos
      have hdB : ringKrullDim B = (d : WithBot ℕ∞) := by
        rw [← Module.supportDim_quotient_eq_ringKrullDim I]
        have hdimQB : Module.supportDim A B = Module.supportDim A A := by
          simpa [B, I, quotientMaximalIdealPowerTorsion, maximalIdealPowerTorsion] using hdimQ
        rw [hdimQB, Module.supportDim_self_eq_ringKrullDim, hd]
      let : Module A B := Module.compHom B (algebraMap A B)
      have : IsScalarTower A B B := IsScalarTower.of_compHom A B B
      have : Module.Finite A B := Module.Finite.of_surjective
        (Algebra.linearMap A B) Ideal.Quotient.mk_surjective
      have hqdepth := depth_quotientMaximalIdealPowerTorsion_pos A A
      have hqSurj : Function.Surjective (algebraMap A B) := Ideal.Quotient.mk_surjective
      have hdepthB : 0 < Module.depth B (IsLocalRing.maximalIdeal B) B := by
        rwa [← @depth_maximalIdeal_eq_of_surjective_algebra A B _ _ _ _ _ B _ _ _
          (IsScalarTower.of_compHom A B B) hqSurj]
      have hposB := min_two_le_depth_of_depth_pos d (by omega) hdB KB hKB ih hdepthB
      have hlin : Functor.Linear A
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))) :=
        DerivedCategory.homologyFunctor_linear (C := ModuleCat.{u} A) A (-(d : ℤ))
      have hzT3 : ∀ j : ℤ, j ≠ 0 →
          IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj T.obj₃) := by
        intro j hj
        let S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (I →ₗ[A] E))
        have hzero : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj S) := by
          have : S.IsGE 0 := inferInstance
          have : S.IsLE 0 := inferInstance
          by_cases hjlt : j < 0
          · exact DerivedCategory.isZero_of_isGE S 0 j hjlt
          · exact DerivedCategory.isZero_of_isLE S 0 j (by omega)
        simpa [T, S] using hzero
      have hIsoMap := isIso_homology_map_mor₁_of_isZero_third T hT (-(d : ℤ))
        (hzT3 (-(d : ℤ) - 1) (by omega)) (hzT3 (-(d : ℤ)) (by omega))
      let F := ModuleCat.restrictScalars q
      let e0 := (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        F (-(d : ℤ))).app KB
      let N := (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (-(d : ℤ))).obj KB
      let : Module A N := Module.compHom N (algebraMap A B)
      have : IsScalarTower A B N := IsScalarTower.of_compHom A B N
      let e1 : ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj T.obj₁) ≃ₗ[A]
          ω :=
        (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).map
          T.mor₁)).toLinearEquiv
      let hiso : ω ≃ₗ[A] N := e1.symm.trans e0.toLinearEquiv
      rw [depth_eq_of_linearEquiv hiso, depth_maximalIdeal_eq_of_surjective_algebra hqSurj]
      exact hposB

/-! ### Serre's condition -/

/-- The localization at `p` of the canonical module is the canonical module of `A_p`, when
`dim(A/p) + dim(A_p) = dim(A)`. -/
private noncomputable def localizedCanonicalModuleEquiv
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    (K : DerivedCategory (ModuleCat.{u} A)) (d e h : ℕ) (hsum : e + h = d) :
    LocalizedModule p.primeCompl
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K) ≃ₗ[
          Localization.AtPrime p]
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.AtPrime p))
        (-(h : ℤ))).obj
          (((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap A (Localization.AtPrime p))).obj K)⟦-(e : ℤ)⟧)) := by
  have hdeg : -(e : ℤ) + -(h : ℤ) = -(d : ℤ) := by omega
  have hsh := homologyShiftIso
    ((StacksDraft.PseudoCoherence.derivedExtensionScalars
      (algebraMap A (Localization.AtPrime p))).obj K) (-(e : ℤ)) (-(h : ℤ))
  rw [hdeg] at hsh
  have eA := ((ModuleCat.restrictScalars
      (algebraMap A (Localization.AtPrime p))).mapIso hsh ≪≫
    localizedHomologyIso p K (-(d : ℤ))).symm.toLinearEquiv
  exact LinearEquiv.ofBijective
    (LinearMap.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
      eA.toLinearMap) eA.bijective

/-- Let `A` be a Noetherian local ring with a normalized dualizing complex `K`, let `d = dim(A)`
and let `ω_A = H^{-d}(K)`. Then `ω_A` satisfies Serre's condition `(S₂)`. -/
@[stacks 0AWE "(2): the canonical module ω_A satisfies Serre's condition (S₂)"]
theorem propertySkModule_canonicalModule {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (K : DerivedCategory (ModuleCat.{u} A))
    (hK : IsNormalizedDualizingComplex.{u, u} K) :
    let d := (ringKrullDim A).unbotD 0 |>.toNat
    let ω := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(d : ℤ))).obj K
    letI : Module.Finite A ω := hK.1.finiteCohomology (-(d : ℤ))
    PropertySkModule A ω 2 := by
  classical
  dsimp only
  intro p hp
  have : p.IsPrime := hp
  let R := Localization.AtPrime p
  let ω := (DerivedCategory.homologyFunctor (ModuleCat.{u} A)
    (-(((ringKrullDim A).unbotD 0).toNat : ℤ))).obj K
  have : Module.Finite A ω := hK.1.finiteCohomology (-(((ringKrullDim A).unbotD 0).toNat : ℤ))
  have hA_lt : ringKrullDim A < ⊤ := ringKrullDim_lt_top_of_isDualizingComplex hK.1
  have hA_bot : ringKrullDim A ≠ ⊥ := fun hbot ↦ not_subsingleton_iff_nontrivial.mpr
    (PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨⟨p, hp⟩⟩)
    (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)
  let d : ℕ := ((ringKrullDim A).unbotD 0).toNat
  have hd : ringKrullDim A = (d : WithBot ℕ∞) :=
    ringKrullDim_eq_natCast_toNat hA_bot (ne_of_lt hA_lt)
  let e : ℕ := ((ringKrullDim (A ⧸ p)).unbotD 0).toNat
  let h : ℕ := ((ringKrullDim R).unbotD 0).toNat
  have hquot_bot : ringKrullDim (A ⧸ p) ≠ ⊥ := fun hbot ↦ not_subsingleton_iff_nontrivial.mpr
    (Ideal.Quotient.nontrivial_iff.mpr hp.ne_top) (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)
  have hquot_top : ringKrullDim (A ⧸ p) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (ringKrullDim_quotient_le p) hA_lt)
  have he : ringKrullDim (A ⧸ p) = (e : WithBot ℕ∞) :=
    ringKrullDim_eq_natCast_toNat hquot_bot hquot_top
  have hR_bot : ringKrullDim R ≠ ⊥ := fun hbot ↦ not_subsingleton_iff_nontrivial.mpr
    (inferInstance : Nontrivial R) (ringKrullDim_eq_bot_iff_subsingleton.mp hbot)
  have hsum := quotient_add_localization_dim_le (A := A) p
  have hR_le : ringKrullDim R ≤ ringKrullDim A :=
    (le_add_of_nonneg_left (ringKrullDim_nonneg_of_nontrivial (R := A ⧸ p))).trans hsum
  have hR_top : ringKrullDim R ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hR_le hA_lt)
  have hh : ringKrullDim R = (h : WithBot ℕ∞) := ringKrullDim_eq_natCast_toNat hR_bot hR_top
  have hsumNat : e + h ≤ d := by
    rw [he, hh, hd] at hsum
    exact_mod_cast hsum
  let N := LocalizedModule.AtPrime p ω
  by_cases hstrict : e + h < d
  · exact propertySkModule_atPrime_of_subsingleton ω p
      (subsingleton_localizedHomology_neg_ringKrullDim K hK p d e h he hh hstrict)
  · have heq : e + h = d := by omega
    by_cases hN : Subsingleton N
    · exact propertySkModule_atPrime_of_subsingleton ω p hN
    · have : Nontrivial N := not_subsingleton_iff_nontrivial.mp hN
      let Kp := ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap A R)).obj K)⟦-(e : ℤ)⟧
      have hKp : IsNormalizedDualizingComplex.{u, u} Kp :=
        isNormalizedDualizingComplex_localizationAtPrime_shift K hK p e he
      have hbound : min (h : ℕ∞) 2 ≤ Module.depth R (IsLocalRing.maximalIdeal R)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(h : ℤ))).obj Kp) :=
        min_two_le_depth_canonicalModule h Kp hKp hh
      have hdepthN : min (h : ℕ∞) 2 ≤ moduleDepth R N := by
        rw [moduleDepth_eq_depth,
          depth_eq_of_linearEquiv (localizedCanonicalModuleEquiv p K d e h heq)]
        exact hbound
      have hsupportN : moduleSupportDim R N ≤ (h : WithBot ℕ∞) := by
        rw [moduleSupportDim_eq_supportDim]
        exact (Module.supportDim_le_ringKrullDim R N).trans (le_of_eq hh)
      have hsupportN_bot : moduleSupportDim R N ≠ ⊥ := by
        rw [moduleSupportDim_eq_supportDim]
        exact Module.supportDim_ne_bot_of_nontrivial (R := R) (M := N)
      have hmin : min (2 : ℕ∞) ((moduleSupportDim R N).unbotD 0) ≤ min 2 (h : ℕ∞) :=
        min_le_min_left _ (WithBot.unbotD_mono hsupportN_bot hsupportN)
      exact hmin.trans (by simpa [min_comm] using hdepthN)

end Dualizing

end
