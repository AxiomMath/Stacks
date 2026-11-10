module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Cech.BaseChange
public import StacksFrontier.RingTheory.Cech.Cohomology
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.Homotopy
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism

/-!
# Flat base change for Koszul and extended alternating Čech complexes

Let `R → S` be flat and induce an isomorphism modulo a finitely generated ideal `I`. If a finite
sequence cuts out the same closed subset of `Spec R` as `I`, then the canonical base-change maps
for its Koszul complex and for its extended alternating Čech complex are quasi-isomorphisms.

## Main results

* `FormalGlueing.quasiIso_koszulSeq_and_cechComplex_baseChange`: both canonical base-change maps
  are quasi-isomorphisms.

## Implementation notes

The complexes over `S` are restricted to `R` in order to express the semilinear base-change maps
as morphisms of complexes. Both complexes are universe-lifted into a common module category.
The Koszul map is characterized on exterior-power generators, and the Čech map is characterized
on every localized fraction in every direct-sum summand: it sends `x / y` in the summand indexed
by `s` to `φ(x) / φ(y)` in the same summand, where `φ = algebraMap R S`. These characterizations
pin down the actual maps to the complexes over `S`, rather than maps only to abstract scalar
extensions.

## References

* [Stacks Project, Tag 091M](https://stacks.math.columbia.edu/tag/091M)
-/

/-! ### Flat base change for Koszul and extended alternating Čech complexes -/

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TensorProduct
open scoped ChangeOfRings

namespace FormalGlueing

universe u uR uS v

private lemma idealPowerTorsion_of_support_subset_zeroLocus
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (I : Ideal R) (hI : I.FG)
    (h : Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    IsIPowerTorsion R M I := by
  intro x
  have hx : PrimeSpectrum.zeroLocus ((R ∙ x).annihilator : Set R) ⊆
      PrimeSpectrum.zeroLocus (I : Set R) := by
    intro p hp
    exact h (Module.mem_support_iff_exists_annihilator.mpr
      ⟨x, (PrimeSpectrum.mem_zeroLocus p _).mp hp⟩)
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hx) hI
  refine ⟨n + 1, Nat.succ_pos _, fun a ha => ?_⟩
  exact (Submodule.mem_annihilator.mp (hn (Ideal.pow_le_pow_right (Nat.le_succ n) ha))) x
    (Submodule.mem_span_singleton_self x)

private lemma extendScalars_additive
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (φ : R →+* S) :
    (ModuleCat.extendScalars.{uR, uS, v} φ).Additive where
  map_add := by
    intro X Y a b
    apply ModuleCat.hom_ext
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul s x => exact TensorProduct.tmul_add s (a x) (b x)
    | add x y hx hy => simp_all only [map_add]

attribute [local instance] extendScalars_additive

/-- `S` as an `R`-module is the restriction of scalars of `S` as an `S`-module. -/
private def restrictScalarsSelfEquiv (R : Type uR) (S : Type uS) [CommRing R] [CommRing S]
    [Algebra R S] :
    S ≃ₗ[R] (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S) :=
  { toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun a s => (algebraMap_smul S a s).symm }

private lemma unitComplex_quasiIso
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] [Algebra R S]
    (hflat : Module.Flat R S) {ι : Type*} (c : ComplexShape ι)
    (C : HomologicalComplex (ModuleCat.{max uR uS v} R) c)
    (hunit : ∀ i, Function.Bijective
      ⇑(ConcreteCategory.hom
        ((ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uS} (algebraMap R S)).unit.app
          (C.homology i)))) :
    QuasiIso
      ((NatTrans.mapHomologicalComplex
        (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uS}
          (algebraMap R S)).unit c).app C) := by
  let F := ModuleCat.extendScalars.{uR, uS, max uR uS v} (algebraMap R S)
  let G := ModuleCat.restrictScalars.{max uR uS v, uR, uS} (algebraMap R S)
  let H := F ⋙ G
  let η : 𝟭 (ModuleCat.{max uR uS v} R) ⟶ H :=
    (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uS} (algebraMap R S)).unit
  let : F.PreservesHomology := by
    let S₀ : ModuleCat R :=
      (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
    have : Module.Flat R S := hflat
    have : Module.Flat R S₀ := Module.Flat.of_linearEquiv (restrictScalarsSelfEquiv R S).symm
    apply ((Functor.exact_tfae F).out 2 3).mp
    intro T hT
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
    exact Module.Flat.lTensor_exact S₀ hT
  have : G.PreservesHomology := Functor.preservesHomologyOfExact G
  let : H.PreservesHomology := {
    preservesKernels {X Y} f := by
      let := Functor.PreservesHomology.preservesKernel F f
      let := Functor.PreservesHomology.preservesKernel G (F.map f)
      infer_instance
    preservesCokernels {X Y} f := by
      let := Functor.PreservesHomology.preservesCokernel F f
      let := Functor.PreservesHomology.preservesCokernel G (F.map f)
      infer_instance }
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : IsIso
      ((ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uS} (algebraMap R S)).unit.app
        (C.homology i)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (hunit i)
  change IsIso (ShortComplex.homologyMap ((C.sc i).mapNatTrans η))
  rw [ShortComplex.homologyMap_mapNatTrans]
  change IsIso (_ ≫
    (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uS} (algebraMap R S)).unit.app
      (C.homology i) ≫ _)
  exact IsIso.comp_isIso' (Iso.isIso_hom _)
    (IsIso.comp_isIso'
      ((ConcreteCategory.isIso_iff_bijective _).2 (hunit i)) (Iso.isIso_inv _))

private lemma unitComplex_quasiIso_of_support
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {ι : Type*} (c : ComplexShape ι)
    (C : HomologicalComplex (ModuleCat.{max uR uS v} R) c)
    (hsupp : ∀ i, Module.support R (C.homology i) ⊆
      PrimeSpectrum.zeroLocus (I : Set R)) :
    QuasiIso
      ((NatTrans.mapHomologicalComplex
        (ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uS}
          (algebraMap R S)).unit c).app C) := by
  refine unitComplex_quasiIso R S hflat c C fun i => ?_
  have h :=
    (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective.{uR, uS, v}
      R S I hflat).mpr hquot
  have h' := h (C.homology i)
    (idealPowerTorsion_of_support_subset_zeroLocus I hI (hsupp i))
  let S₀ : ModuleCat R :=
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let eS := restrictScalarsSelfEquiv R S
  let e : ((C.homology i) ⊗[R] S) ≃ₗ[R]
      ((ModuleCat.extendScalars (algebraMap R S) ⋙
        ModuleCat.restrictScalars (algebraMap R S)).obj (C.homology i)) :=
    (TensorProduct.congr (LinearEquiv.refl R (C.homology i)) eS).trans
      (TensorProduct.comm R (C.homology i) S₀)
  have hb : Function.Bijective (fun x : C.homology i => e (x ⊗ₜ[R] (1 : S))) :=
    e.bijective.comp h'
  change Function.Bijective
    (fun x : C.homology i =>
      ((ModuleCat.extendRestrictScalarsAdj.{max uR v, uR, uS} (algebraMap R S)).unit.app
        (C.homology i)).hom x)
  have he (x : C.homology i) : e (x ⊗ₜ[R] (1 : S)) =
      ((1 : S) ⊗ₜ[R, algebraMap R S] x) := by
    simp only [e, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply]
    rfl
  simpa only [he, ModuleCat.extendRestrictScalarsAdj_unit_app_apply] using hb

private lemma koszul_homology_support
    {R : Type*} [CommRing R] {r : ℕ} (f : Fin r → R) (n : ℕ) :
    Module.support R ((Koszul.seqComplex f).homology n) ⊆
      PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set R) := by
  intro p hp
  exact (PrimeSpectrum.mem_zeroLocus p _).mpr <|
    (Koszul.koszulSeq_smul_nullHomotopic_and_span_le_annihilator f).2 n |>.trans
      (Module.annihilator_le_of_mem_support hp)

private lemma cech_homology_support
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (n : ℕ) :
    Module.support R ((Cech.cechComplex f R).homology n) ⊆
      PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set R) := by
  let e := (Cech.cechComplex f R).extendHomologyIso
    ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) (by simp)
  rw [← e.toLinearEquiv.support_eq]
  exact (Cech.cechComplex_homology_torsion_support_vanishes f R (n : ℤ)).2.2.1

private noncomputable def scalarExtensionEquiv
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] [Algebra R S]
    (M : Type v) [AddCommGroup M] [Module R M] :
    ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)) ≃ₗ[S]
      (S ⊗[R] M) := by
  let S₀ : ModuleCat R :=
    (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let eS := restrictScalarsSelfEquiv R S
  let e : (S₀ ⊗[R] M) ≃ₗ[R] (S ⊗[R] M) :=
    TensorProduct.congr eS.symm (LinearEquiv.refl R M)
  let L : ((ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R M)) →ₗ[S]
      (S ⊗[R] M) :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := by
        intro s x
        induction x using TensorProduct.inductionOn with
        | tmul a m =>
          change e ((s * (show S from a)) ⊗ₜ[R, algebraMap R S] m) =
            s • e (a ⊗ₜ[R, algebraMap R S] m)
          simp only [e, TensorProduct.congr_tmul,
            eS, LinearEquiv.refl_apply, TensorProduct.smul_tmul']
          rfl
        | add x y hx hy =>
          change e (s • (x + y : (ModuleCat.extendScalars (algebraMap R S)).obj
            (ModuleCat.of R M))) = _
          rw [smul_add, map_add, hx, hy, map_add, smul_add] }
  exact LinearEquiv.ofBijective L e.bijective

private lemma support_uliftComplex
    {R : Type uR} [CommRing R] {ι : Type*} {c : ComplexShape ι}
    (C : HomologicalComplex (ModuleCat.{v} R) c) (n : ι) :
    Module.support R
      (((ModuleCat.uliftFunctor.{uS} R).mapHomologicalComplex c).obj C |>.homology n) =
      Module.support R (C.homology n) := by
  let F := ModuleCat.uliftFunctor.{uS, v} R
  let : F.PreservesHomology := Functor.preservesHomologyOfExact F
  exact (((C.sc n).mapHomologyIso F).toLinearEquiv.trans ULift.moduleEquiv).support_eq

private lemma koszul_baseChange_iso
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) :
    let C := ((ModuleCat.uliftFunctor.{uS} R).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Koszul.seqComplex f)
    let D := ((ModuleCat.uliftFunctor.{uR} S).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (Koszul.seqComplex (fun i => algebraMap R S (f i)))
    ∃ e : ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj C ≅ D,
      ∀ n (v : Fin n → (Fin r → R)),
        e.hom.f n ((1 : S) ⊗ₜ[R, algebraMap R S] ULift.up (exteriorPower.ιMulti R n v)) =
          ULift.up (exteriorPower.ιMulti S n (fun i j => algebraMap R S (v i j))) := by
  dsimp only
  choose β hβ using fun n => KoszulC.extPow_baseChange_natEquiv
    (R := R) (S := S) (r := r) n
  let E (n : ℕ) :=
    ((scalarExtensionEquiv R S (ULift.{uS} (⋀[R]^n (Fin r → R)))).trans
      ((AlgebraTensorModule.congr (LinearEquiv.refl S S) ULift.moduleEquiv).trans
        ((β n).trans ULift.moduleEquiv.symm)))
  have hE (n : ℕ) (s : S) (x : ⋀[R]^n (Fin r → R)) :
      E n (s ⊗ₜ[R, algebraMap R S] ULift.up x) = ULift.up (β n (s ⊗ₜ[R] x)) := rfl
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun n => (E n).toModuleIso) ?_, ?_⟩
  · intro i j hij
    obtain rfl : j + 1 = i := hij
    simp only [Functor.mapHomologicalComplex_obj_d, Koszul.seqComplex_d]
    apply ModuleCat.ExtendScalars.hom_ext
    rintro ⟨x⟩
    change ULift.up (Koszul.d (Koszul.seqDual (fun k => algebraMap R S (f k))) j
        (β (j + 1) ((1 : S) ⊗ₜ[R] x))) =
      ULift.up (β j ((1 : S) ⊗ₜ[R] (Koszul.d (Koszul.seqDual f) j x)))
    rw [KoszulC.d_baseChange_comm f β hβ]
  · intro n v
    change E n ((1 : S) ⊗ₜ[R, algebraMap R S] ULift.up (exteriorPower.ιMulti R n v)) = _
    rw [hE, hβ]

private noncomputable def localizedModuleCongr
    {A : Type*} [CommRing A] (T : Submonoid A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) : LocalizedModule T M ≃ₗ[A] LocalizedModule T N :=
  LinearEquiv.ofBijective ((LocalizedModule.map T e.toLinearMap).restrictScalars A)
    ⟨LocalizedModule.map_injective T _ e.injective,
      LocalizedModule.map_surjective T _ e.surjective⟩

private lemma localizedModuleCongr_mk
    {A : Type*} [CommRing A] (T : Submonoid A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (x : M) (y : T) :
    localizedModuleCongr T e (LocalizedModule.mk x y) = LocalizedModule.mk (e x) y :=
  LocalizedModule.map_mk T e.toLinearMap x y

private lemma localizedModuleCongr_cechι
    {A : Type*} [CommRing A] {r : ℕ} (f : Fin r → A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) {s t : Finset (Fin r)} (h : s ⊆ t) (x : Cech.cechMod f M s) :
    localizedModuleCongr (Cech.cechSub f t) e (Cech.cechι f M h x) =
      Cech.cechι f N h (localizedModuleCongr (Cech.cechSub f s) e x) := by
  apply LinearMap.congr_fun (show
    (localizedModuleCongr (Cech.cechSub f t) e).toLinearMap.comp (Cech.cechι f M h) =
      (Cech.cechι f N h).comp (localizedModuleCongr (Cech.cechSub f s) e).toLinearMap from ?_) x
  apply IsLocalizedModule.ext (Cech.cechSub f s)
    (LocalizedModule.mkLinearMap (Cech.cechSub f s) M)
    (Cech.isUnit_algebraMap f N h (LocalizedModule.mkLinearMap (Cech.cechSub f t) N))
  ext m
  change localizedModuleCongr (Cech.cechSub f t) e
    (Cech.cechι f M h (LocalizedModule.mkLinearMap (Cech.cechSub f s) M m)) = _
  rw [Cech.cechι_mk]
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply,
    LinearEquiv.coe_coe, localizedModuleCongr_mk]
  exact (Cech.cechι_mk f N h (e m)).symm

private noncomputable def cechTermCongr
    {A : Type*} [CommRing A] {r : ℕ} (f : Fin r → A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (p : ℕ) : Cech.cechTerm f M p ≃ₗ[A] Cech.cechTerm f N p :=
  DirectSum.congrLinearEquiv fun s => localizedModuleCongr (Cech.cechSub f s.1) e

private lemma cechTermCongr_lof
    {A : Type*} [CommRing A] {r : ℕ} (f : Fin r → A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (p : ℕ) (s : {t : Finset (Fin r) // t.card = p})
    (x : Cech.cechMod f M s.1) :
    cechTermCongr f e p (DirectSum.lof A _ _ s x) =
      DirectSum.lof A _ _ s (localizedModuleCongr (Cech.cechSub f s.1) e x) := by
  simp [cechTermCongr, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]

private lemma cechTermCongr_comm_d
    {A : Type*} [CommRing A] {r : ℕ} (f : Fin r → A)
    {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (e : M ≃ₗ[A] N) (p : ℕ) (x : Cech.cechTerm f M p) :
    cechTermCongr f e (p + 1) (Cech.cechD f M p x) =
      Cech.cechD f N p (cechTermCongr f e p x) := by
  apply LinearMap.congr_fun (show
    (cechTermCongr f e (p + 1)).toLinearMap.comp (Cech.cechD f M p) =
      (Cech.cechD f N p).comp (cechTermCongr f e p).toLinearMap from ?_) x
  apply DirectSum.linearMap_ext
  intro s
  apply LinearMap.ext
  intro y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Cech.cechD_lof,
    map_sum, cechTermCongr_lof]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_zsmul, cechTermCongr_lof, localizedModuleCongr_cechι]

private lemma cech_baseChange_iso
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) :
    let C := ((ModuleCat.uliftFunctor.{uS} R).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (Cech.cechComplex f R)
    let D := ((ModuleCat.uliftFunctor.{uR} S).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (Cech.cechComplex (fun i => algebraMap R S (f i)) S)
    ∃ e : ((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj C ≅ D,
      ∀ p (x : Cech.cechTerm f R p),
        e.hom.f p ((1 : S) ⊗ₜ[R, algebraMap R S] ULift.up x) =
          ULift.up (cechTermCongr (fun i => algebraMap R S (f i))
            (AlgebraTensorModule.rid R S S) p
              (Stacks.CechBaseChange.termBaseChangeR f R S p x)) := by
  dsimp only
  let γ (p : ℕ) := cechTermCongr (fun i => algebraMap R S (f i))
    (AlgebraTensorModule.rid R S S) p
  let E (p : ℕ) :=
    (scalarExtensionEquiv R S (ULift.{uS} (Cech.cechTerm f R p))).trans
      ((AlgebraTensorModule.congr (LinearEquiv.refl S S) ULift.moduleEquiv).trans
        ((Stacks.CechBaseChange.termBaseChangeEquiv f R S p).trans
          ((γ p).trans ULift.moduleEquiv.symm)))
  have hE (p : ℕ) (s : S) (x : Cech.cechTerm f R p) :
      E p (s ⊗ₜ[R, algebraMap R S] ULift.up x) =
        ULift.up (γ p (Stacks.CechBaseChange.termBaseChangeS f R S p (s ⊗ₜ[R] x))) := rfl
  refine ⟨HomologicalComplex.Hom.isoOfComponents (fun p => (E p).toModuleIso) ?_, ?_⟩
  · intro i j hij
    obtain rfl : i + 1 = j := hij
    simp only [Functor.mapHomologicalComplex_obj_d, Cech.cechComplex, CochainComplex.of_d]
    apply ModuleCat.ExtendScalars.hom_ext
    rintro ⟨x⟩
    change ULift.up (Cech.cechD _ S i
        (γ i (Stacks.CechBaseChange.termBaseChangeS f R S i ((1 : S) ⊗ₜ[R] x)))) =
      ULift.up (γ (i + 1) (Stacks.CechBaseChange.termBaseChangeS f R S (i + 1)
        ((1 : S) ⊗ₜ[R] (Cech.cechD f R i x))))
    rw [← cechTermCongr_comm_d]
    congr 2
    exact (LinearMap.congr_fun (Stacks.CechBaseChange.termBaseChangeS_comm_d f R S i)
      ((1 : S) ⊗ₜ[R] x)).symm
  · intro p x
    change E p ((1 : S) ⊗ₜ[R, algebraMap R S] ULift.up x) = _
    rw [hE, Stacks.CechBaseChange.termBaseChangeS_tmul, one_smul]

private lemma baseChangeR_mk
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (s : Finset (Fin r)) (x : R) (y : Cech.cechSub f s) :
    localizedModuleCongr (Cech.cechSub (fun i => algebraMap R S (f i)) s)
        (AlgebraTensorModule.rid R S S)
        (Stacks.CechBaseChange.baseChangeR f R S s (LocalizedModule.mk x y)) =
      LocalizedModule.mk (algebraMap R S x)
        ⟨algebraMap R S y, by
          obtain ⟨n, hn⟩ := y.2
          exact ⟨n, by rw [← hn, map_pow, map_prod]⟩⟩ := by
  let g := fun i => algebraMap R S (f i)
  let y' : Cech.cechSub g s := ⟨algebraMap R S y, by
    obtain ⟨n, hn⟩ := y.2
    exact ⟨n, by rw [← hn, map_pow, map_prod]⟩⟩
  apply IsLocalizedModule.smul_injective (LocalizedModule.mkLinearMap (Cech.cechSub g s) S) y'
  change (y' : S) • (localizedModuleCongr (Cech.cechSub g s) (AlgebraTensorModule.rid R S S)
    (Stacks.CechBaseChange.baseChangeR f R S s (LocalizedModule.mk x y))) =
      (y' : S) • LocalizedModule.mk (algebraMap R S x) y'
  rw [← map_smul, algebraMap_smul, ← map_smul]
  have hx : (y : R) • LocalizedModule.mk x y = LocalizedModule.mk x 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel y x
  have hy : (y' : S) • LocalizedModule.mk (algebraMap R S x) y' =
      LocalizedModule.mk (algebraMap R S x) 1 := by
    rw [LocalizedModule.smul'_mk]
    exact LocalizedModule.mk_cancel y' (algebraMap R S x)
  rw [hx, hy]
  rw [Stacks.CechBaseChange.baseChangeR, LocalizedModule.lift_mk_one]
  simp only [LinearMap.comp_apply,
    LinearMap.coe_restrictScalars, TensorProduct.mk_apply, LocalizedModule.mkLinearMap_apply,
    localizedModuleCongr_mk, AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one]

/-- If a flat map `R → S` is an isomorphism modulo a finitely generated ideal `I`, then for
every finite sequence defining the same closed subset as `I`, the canonical base-change maps on
the Koszul complex and on the extended alternating Čech complex are quasi-isomorphisms. -/
@[stacks 091M]
public theorem quasiIso_koszulSeq_and_cechComplex_baseChange
    (R : Type uR) (S : Type uS) [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (hI : I.FG) (hflat : Module.Flat R S)
    (hquot : Function.Bijective
      (Ideal.quotientMap (I.map (algebraMap R S)) (algebraMap R S) Ideal.le_comap_map))
    {r : ℕ} (f : Fin r → R)
    (hV : PrimeSpectrum.zeroLocus (Ideal.span (Set.range f) : Set R) =
      PrimeSpectrum.zeroLocus (I : Set R)) :
    let liftR := (ModuleCat.uliftFunctor.{uS, uR} R)
    let liftS := (ModuleCat.uliftFunctor.{uR, uS} S)
    let koszulR := (liftR.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Koszul.seqComplex f)
    let koszulS := (liftS.mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (Koszul.seqComplex (fun i => algebraMap R S (f i)))
    let cechR := (liftR.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Cech.cechComplex f R)
    let cechS := (liftS.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Cech.cechComplex (fun i => algebraMap R S (f i)) S)
    ∃ k : koszulR ⟶
          ((ModuleCat.restrictScalars.{max uR uS} (algebraMap R S)).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj koszulS,
      (∀ (n : ℕ) (v : Fin n → (Fin r → R)),
          k.f n (ULift.up (exteriorPower.ιMulti R n v)) =
            ULift.up (exteriorPower.ιMulti S n (fun i j => algebraMap R S (v i j)))) ∧
      QuasiIso k ∧
      ∃ c : cechR ⟶
          ((ModuleCat.restrictScalars.{max uR uS} (algebraMap R S)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj cechS,
        (∀ (p : ℕ) (s : {t : Finset (Fin r) // t.card = p}) (x : R)
            (y : Cech.cechSub f s.1),
            c.f p
                (ULift.up (DirectSum.lof R {t : Finset (Fin r) // t.card = p}
                  (fun t => Cech.cechMod f R t.1) s
                  (LocalizedModule.mk x y))) =
              ULift.up (DirectSum.lof S {t : Finset (Fin r) // t.card = p}
                (fun t => Cech.cechMod (fun i => algebraMap R S (f i)) S t.1) s
                (LocalizedModule.mk (algebraMap R S x)
                  ⟨algebraMap R S y, by
                    obtain ⟨n, hn⟩ := y.2
                    exact ⟨n, by rw [← hn, map_pow, map_prod]⟩⟩))) ∧
        QuasiIso c := by
  dsimp only
  let liftR := ModuleCat.uliftFunctor.{uS, uR} R
  let liftS := ModuleCat.uliftFunctor.{uR, uS} S
  let G := ModuleCat.restrictScalars.{max uR uS} (algebraMap R S)
  let K := (liftR.mapHomologicalComplex (ComplexShape.down ℕ)).obj (Koszul.seqComplex f)
  let C := (liftR.mapHomologicalComplex (ComplexShape.up ℕ)).obj (Cech.cechComplex f R)
  let ηK := (NatTrans.mapHomologicalComplex
    (ModuleCat.extendRestrictScalarsAdj.{uR, uR, uS} (algebraMap R S)).unit
      (ComplexShape.down ℕ)).app K
  let ηC := (NatTrans.mapHomologicalComplex
    (ModuleCat.extendRestrictScalarsAdj.{uR, uR, uS} (algebraMap R S)).unit
      (ComplexShape.up ℕ)).app C
  have hK : QuasiIso ηK :=
    unitComplex_quasiIso_of_support.{uR, uS, 0} R S I hI hflat hquot _ _ fun n => by
      rw [support_uliftComplex, ← hV]
      exact koszul_homology_support f n
  have hC : QuasiIso ηC :=
    unitComplex_quasiIso_of_support.{uR, uS, 0} R S I hI hflat hquot _ _ fun n => by
      rw [support_uliftComplex, ← hV]
      exact cech_homology_support f n
  obtain ⟨eK, heK⟩ := koszul_baseChange_iso R S f
  obtain ⟨eC, heC⟩ := cech_baseChange_iso R S f
  let k := ηK ≫ (G.mapHomologicalComplex (ComplexShape.down ℕ)).map eK.hom
  let c := ηC ≫ (G.mapHomologicalComplex (ComplexShape.up ℕ)).map eC.hom
  refine ⟨k, heK, inferInstance, c, ?_, inferInstance⟩
  · intro p s x y
    change eC.hom.f p ((1 : S) ⊗ₜ[R, algebraMap R S] ULift.up
      (DirectSum.lof R _ _ s (LocalizedModule.mk x y))) = _
    rw [heC, Stacks.CechBaseChange.termBaseChangeR, DirectSum.toModule_lof, LinearMap.comp_apply]
    change ULift.up (cechTermCongr (fun i => algebraMap R S (f i))
      (AlgebraTensorModule.rid R S S) p
      (DirectSum.lof S _ _ s
        (Stacks.CechBaseChange.baseChangeR f R S s.1 (LocalizedModule.mk x y)))) = _
    rw [cechTermCongr_lof, baseChangeR_mk]

end FormalGlueing

end

end
