module

public import Mathlib.Algebra.Category.ModuleCat.Localization
import all StacksFrontier.Algebra.Module.Projective.Invertible
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.KTheory.Grothendieck.Determinant
public import StacksFrontier.KTheory.Grothendieck.PerfectComplex
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.SyzygyFreeLocus
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension
public import StacksFrontier.RingTheory.RegularLocalRing.MaximalCohenMacaulay
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension

/-!
# A regular local ring is a unique factorization domain

Let `R` be a regular local ring and `f ∈ R`. An invertible `R_f`-module `L` is the localization
of a finite `R`-module, which has a finite free resolution because `R` is regular. Localizing
that resolution presents `L` as a bounded complex of finite free `R_f`-modules, so in `K₀(R_f)`
the class of `L` is an alternating sum of classes of free modules. The determinant
`K₀(R_f) → Pic(R_f)` vanishes on free modules and sends the class of `L` to the class of `L`, so
`L` is free: the Picard group of `R_f` is trivial. Triviality of these Picard groups drives an
induction on the dimension: for a regular parameter `x`, which is prime, the localizations of
`R_x` at its maximal ideals are regular local rings of smaller dimension, and a Noetherian domain
with trivial Picard group that is locally a unique factorization domain is one. Nagata's
criterion then passes from `R_x` back to `R`.

## Main results

* `IsRegularLocalRing.pic_subsingleton_localization_away`: the Picard group of a localization of
  a regular local ring at an element is trivial.
* `IsRegularLocalRing.uniqueFactorizationMonoid`: a regular local ring is a unique factorization
  domain.
* `UniqueFactorizationMonoid.of_localization_maximal_of_pic_subsingleton`: a Noetherian domain
  with trivial Picard group whose localizations at maximal ideals are unique factorization
  domains is a unique factorization domain.

## Implementation notes

The `K`-theoretic input is the determinant homomorphism `K₀(A) → Pic(A)` together with the Euler
characteristic of a perfect complex: the Euler characteristic of the localized free resolution
is the class of `L` in `K₀(R_f)`. In the induction, every localization of `R_x` at a maximal
ideal is a localization of `R` at a prime of smaller height, and Nagata's criterion is
`UniqueFactorizationMonoid.iff_localizationAway_of_prime`.

## References

* [Stacks Project, Tag 0AFZ](https://stacks.math.columbia.edu/tag/0AFZ)
* [Stacks Project, Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0)
-/

namespace IsRegularLocalRing

/-! ### The Picard group of a localization at an element -/

section

universe u

open CategoryTheory Limits IsLocalRing

private theorem det_zero_iff_free {A : Type u} [CommRing A]
    (det : K0 A →+ Additive (CommRing.Pic A))
    (hdet : ∀ (M : FGProj A) (n : ℕ),
      Module.rankAtStalk M.carrier = Function.const (PrimeSpectrum A) n →
        ∃ h : Module.Invertible A (⋀[A]^n M.carrier),
          det (K0.mk M) =
            Additive.ofMul (@CommRing.Pic.mk A (⋀[A]^n M.carrier) inferInstance
              inferInstance inferInstance h))
    (L : Type u) [AddCommGroup L] [Module A L] [Module.Invertible A L]
    (hzero : det (K0.mk ({ carrier := L } : FGProj A)) = 0) : Module.Free A L := by
  have hrank : Module.rankAtStalk L = Function.const (PrimeSpectrum A) 1 := by
    funext p
    simp [Module.rankAtStalk, Module.Invertible.finrank_eq_one]
  obtain ⟨h, hh⟩ := hdet ({carrier := L} : FGProj A) 1 hrank
  rw [hh] at hzero
  have heq : CommRing.Pic.mk A (⋀[A]^1 L) = 1 := hzero
  have hfree : Module.Free A (⋀[A]^1 L) := CommRing.Pic.mk_eq_one_iff_free.mp heq
  exact Module.Free.of_equiv (exteriorPower.oneEquiv A L)

private theorem single_finite_projective {A L : Type u} [CommRing A]
    [AddCommGroup L] [Module A L] [Module.Finite A L] [Module.Projective A L]
    (i : ℤ) :
    Module.Finite A (((CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj
      (ModuleCat.of A L)).X i) ∧
    Module.Projective A (((CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj
      (ModuleCat.of A L)).X i) := by
  let Ps := (CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj
    (ModuleCat.of A L)
  show Module.Finite A (Ps.X i) ∧ Module.Projective A (Ps.X i)
  by_cases hi : i = 0
  · subst i
    let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
      (ModuleCat.of A L)).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
  · have hz := HomologicalComplex.isZero_single_obj_X
      (ComplexShape.up ℤ) (0 : ℤ) (ModuleCat.of A L) i hi
    let : Subsingleton (((CochainComplex.singleFunctor (ModuleCat.{u} A)
      (0 : ℤ)).obj (ModuleCat.of A L)).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    exact ⟨inferInstance, Module.Projective.of_free⟩

private noncomputable def localized_equiv (R : Type u) [CommRing R] (f : R)
    (M L : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup L] [Module (Localization.Away f) L]
    [Module R L] [IsScalarTower R (Localization.Away f) L]
    (g : M →ₗ[R] L) (hbc : IsBaseChange (Localization.Away f) g) :
    ((ModuleCat.of R M).localizedModule (Submonoid.powers f)) ≃ₗ[Localization.Away f] L := by
  letI : IsLocalizedModule (Submonoid.powers f) g :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) (Localization.Away f) g).mpr hbc
  letI : IsLocalizedModule (Submonoid.powers f)
      ((ModuleCat.of R M).localizedModuleMkLinearMap (Submonoid.powers f)) :=
    ModuleCat.localizedModule_isLocalizedModule _ _
  exact IsLocalizedModule.mapEquiv (Submonoid.powers f)
    ((ModuleCat.of R M).localizedModuleMkLinearMap (Submonoid.powers f)) g
    (Localization.Away f) (LinearEquiv.refl R M)

private theorem cochain_ge_of_bounded {A : Type u} [CommRing A] {X : ModuleCat.{u} A}
    (P : ProjectiveResolution X) (d : ℕ)
    (hbound : ∀ n, d < n → IsZero (P.complex.X n)) :
    P.cochainComplex.IsStrictlyGE (-(d : ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  by_cases hi0 : i ≤ 0
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hi0
    have hdn : d < n := by omega
    exact IsZero.of_iso (hbound n hdn) (P.cochainComplexXIso (-n) n)
  · exact P.cochainComplex.isZero_of_isStrictlyLE 0 i (by omega)

private theorem cochain_finite_free {A : Type u} [CommRing A] {X : ModuleCat.{u} A}
    (P : ProjectiveResolution X)
    (hP : ∀ n, Module.Finite A (P.complex.X n) ∧ Module.Free A (P.complex.X n))
    (i : ℤ) : Module.Finite A (P.cochainComplex.X i) ∧
      Module.Free A (P.cochainComplex.X i) := by
  by_cases hi : i ≤ 0
  · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hi
    let e := (P.cochainComplexXIso (-n) n).toLinearEquiv
    let : Module.Finite A (P.complex.X n) := (hP n).1
    let : Module.Free A (P.complex.X n) := (hP n).2
    exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩
  · have hz : IsZero (P.cochainComplex.X i) :=
      P.cochainComplex.isZero_of_isStrictlyLE 0 i (by omega)
    let : Subsingleton (P.cochainComplex.X i) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    exact ⟨inferInstance, Module.Free.of_subsingleton _ _⟩

private noncomputable def map_resolution (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (f : R) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CategoryTheory.ObjectProperty.LeftResolution
      (fun N : ModuleCat.{u} R => Module.Free R N ∧ Module.Finite R N)
      (ModuleCat.of R M)) :
    ProjectiveResolution ((ModuleCat.localizedModuleFunctor (Submonoid.powers f)).obj
      (ModuleCat.of R M)) := by
  let G := ModuleCat.localizedModuleFunctor (Submonoid.powers f)
  let P : ProjectiveResolution (ModuleCat.of R M) :=
    F.toProjectiveResolution (fun n =>
      letI := (F.property n).1
      (IsProjective.iff_projective (F.complex.X n)).mp Module.Projective.of_free)
  exact {
    complex := (G.mapHomologicalComplex _).obj P.complex
    projective := by
      intro n
      change Projective ((F.complex.X n).localizedModule (Submonoid.powers f))
      let : Module.Free R (F.complex.X n) := (F.property n).1
      let : Module.Free (Localization (Submonoid.powers f))
          ((F.complex.X n).localizedModule (Submonoid.powers f)) :=
        Module.Free.of_isLocalizedModule (Submonoid.powers f)
          ((F.complex.X n).localizedModuleMkLinearMap (Submonoid.powers f))
      have : Module.Projective (Localization (Submonoid.powers f))
          ((F.complex.X n).localizedModule (Submonoid.powers f)) :=
        Module.Projective.of_free
      exact (IsProjective.iff_projective _).mp this
    π := (G.mapHomologicalComplex _).map P.π ≫
      (HomologicalComplex.singleMapHomologicalComplex _ _ _).hom.app _
    quasiIso := inferInstance
  }

private theorem mapped_resolution_bounded (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (f : R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CategoryTheory.ObjectProperty.LeftResolution
      (fun N : ModuleCat.{u} R => Module.Free R N ∧ Module.Finite R N)
      (ModuleCat.of R M)) (d : ℕ)
    (hF : ∀ n, d < n → IsZero (F.complex.X n)) :
    (map_resolution R f M F).cochainComplex.IsStrictlyGE (-(d : ℤ)) := by
  apply cochain_ge_of_bounded
  intro n hn
  show IsZero ((ModuleCat.localizedModuleFunctor (Submonoid.powers f)).obj
    (F.complex.X n))
  let G := ModuleCat.localizedModuleFunctor (Submonoid.powers f)
  exact IsZero.of_iso (isZero_zero _) (G.mapIso (hF n hn).isoZero ≪≫ G.mapZeroObject)

private theorem mapped_resolution_finite_free (R : Type u) [CommRing R]
    [IsRegularLocalRing R] (f : R)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CategoryTheory.ObjectProperty.LeftResolution
      (fun N : ModuleCat.{u} R => Module.Free R N ∧ Module.Finite R N)
      (ModuleCat.of R M)) (n : ℕ) :
    Module.Finite (Localization.Away f) ((map_resolution R f M F).complex.X n) ∧
      Module.Free (Localization.Away f) ((map_resolution R f M F).complex.X n) := by
  let : Module.Free R (F.complex.X n) := (F.property n).1
  let : Module.Finite R (F.complex.X n) := (F.property n).2
  show Module.Finite (Localization.Away f)
      ((F.complex.X n).localizedModule (Submonoid.powers f)) ∧
    Module.Free (Localization.Away f)
      ((F.complex.X n).localizedModule (Submonoid.powers f))
  exact ⟨Module.Finite.of_isLocalizedModule (Submonoid.powers f)
    ((F.complex.X n).localizedModuleMkLinearMap (Submonoid.powers f)),
    Module.Free.of_isLocalizedModule (Submonoid.powers f)
    ((F.complex.X n).localizedModuleMkLinearMap (Submonoid.powers f))⟩

private theorem exists_resolution (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (d : ℕ) (F : CategoryTheory.ObjectProperty.LeftResolution
      (fun N : ModuleCat.{u} R => Module.Free R N ∧ Module.Finite R N)
      (ModuleCat.of R M)),
      ∀ i, d < i → IsZero (F.complex.X i) := by
  let : IsLocalRing R := IsRegularLocalRing.toIsLocalRing
  let d := Module.finrank (IsLocalRing.ResidueField R) (CotangentSpace R)
  have hdim : ringKrullDim R ≤ (d : WithBot ℕ∞) :=
    ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).ge
  obtain ⟨F, hF⟩ :=
    (IsRegularLocalRing.exists_leftResolution_free_finite_and_hasProjectiveDimensionLE hdim).1
      (ModuleCat.of R M) 0 (by simp)
  exact ⟨d, F, by simpa using hF⟩

private lemma det_mk_eq_zero_of_free {A : Type u} [CommRing A]
    (det : K0 A →+ Additive (CommRing.Pic A))
    (hdet : ∀ (M : FGProj A) (n : ℕ),
      Module.rankAtStalk M.carrier = Function.const (PrimeSpectrum A) n →
        ∃ h : Module.Invertible A (⋀[A]^n M.carrier),
          det (K0.mk M) =
            Additive.ofMul (@CommRing.Pic.mk A (⋀[A]^n M.carrier) inferInstance
              inferInstance inferInstance h))
    (M : FGProj A) [Module.Free A M.carrier] : det (K0.mk M) = 0 := by
  obtain ⟨h, hh⟩ := hdet M (Module.finrank A M.carrier) (by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    rfl)
  rw [hh]
  show CommRing.Pic.mk A (⋀[A]^(Module.finrank A M.carrier) M.carrier) = 1
  exact CommRing.Pic.mk_eq_one_iff_free.mpr inferInstance

private theorem free_of_bounded_free_complex {A L : Type u} [CommRing A]
    [AddCommGroup L] [Module A L] [Module.Invertible A L]
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    (hge : P.IsStrictlyGE a) (hle : P.IsStrictlyLE b)
    (hfinite : ∀ i, Module.Finite A (P.X i))
    (hfree : ∀ i, Module.Free A (P.X i))
    (hiso : Nonempty (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A L)) ≅
      DerivedCategory.Q.obj P)) : Module.Free A L := by
  let hprojective : ∀ i, Module.Projective A (P.X i) := fun i => by
    let := hfree i
    exact Module.Projective.of_free
  obtain ⟨det, hdet⟩ := K0.exists_determinant_hom A
  obtain ⟨c, -, -, hc⟩ := K0.exists_eulerChar_perfect A
  let Ps := (CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).obj (ModuleCat.of A L)
  let K := DerivedCategory.Q.obj Ps
  have hK : StacksDraft.Perfect.IsPerfect K :=
    ⟨P, a, b, hge, hle, hfinite, hprojective, hiso⟩
  have hfp := single_finite_projective (A := A) (L := L)
  have hsingleCalc := hc K hK Ps 0 0 (by infer_instance) (by infer_instance)
    (fun i => (hfp i).1) (fun i => (hfp i).2) ⟨Iso.refl _⟩
  let : Module.Finite A (Ps.X 0) := (hfp 0).1
  let : Module.Projective A (Ps.X 0) := (hfp 0).2
  let M0 : FGProj A := {carrier := Ps.X 0}
  have hsingle : c ⟨K, hK⟩ = K0.mk ({carrier := L} : FGProj A) := by
    have heq : c ⟨K, hK⟩ = K0.mk M0 := by simpa [M0] using hsingleCalc
    exact heq.trans (K0.mk_eq_of_iso M0 ({carrier := L} : FGProj A)
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (ModuleCat.of A L)).toLinearEquiv)
  have hcalc := hc K hK P a b hge hle hfinite hprojective hiso
  have hdetP (i : ℤ) :
      det (K0.mk
        ({carrier := P.X i, finite := hfinite i, projective := hprojective i} : FGProj A)) = 0 := by
    let : Module.Free A (P.X i) := hfree i
    exact det_mk_eq_zero_of_free det hdet _
  have hdetL : det (K0.mk ({carrier := L} : FGProj A)) = 0 := by
    rw [← hsingle, hcalc, map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_zsmul, hdetP i, smul_zero]
  exact det_zero_iff_free det hdet L hdetL

/-- **Stacks 0AFZ.** The Picard group of the localization of a regular local ring at an
element is trivial. -/
@[stacks 0AFZ]
public theorem pic_subsingleton_localization_away
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (f : R) :
    Subsingleton (CommRing.Pic (Localization.Away f)) := by
  let A := Localization.Away f
  apply CommRing.Pic.subsingleton_iff.mpr
  intro L _ _ _
  let : Module R L := Module.compHom L (algebraMap R A)
  let : IsScalarTower R A L := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  obtain ⟨M, hMadd, hMmod, g, hMfin, hbc⟩ :=
    (Module.exists_finite_isBaseChange_of_surjective_algebraMap
      (Submonoid.powers f) A L (R' := A) Function.surjective_id)
  let : AddCommGroup M := hMadd
  let : Module R M := hMmod
  let : Module.Finite R M := hMfin
  obtain ⟨d, F, hF⟩ := exists_resolution R M
  let P := map_resolution R f M F
  have hfinitefree : ∀ i, Module.Finite A (P.cochainComplex.X i) ∧
      Module.Free A (P.cochainComplex.X i) :=
    cochain_finite_free P (mapped_resolution_finite_free R f M F)
  let e : ((ModuleCat.of R M).localizedModule (Submonoid.powers f)) ≃ₗ[A] L :=
    localized_equiv R f M L g hbc.1
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
    HasDerivedCategory.standard (ModuleCat.{u} A)
  let e0 : ((ModuleCat.localizedModuleFunctor (Submonoid.powers f)).obj
      (ModuleCat.of R M)) ≅ ModuleCat.of A L := e.toModuleIso
  let eSingle := (CochainComplex.singleFunctor (ModuleCat.{u} A) (0 : ℤ)).mapIso e0
  let eDerived : DerivedCategory.Q.obj P.cochainComplex ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A L)) :=
    (asIso (DerivedCategory.Q.map P.π')) ≪≫ DerivedCategory.Q.mapIso eSingle
  exact free_of_bounded_free_complex P.cochainComplex (-(d : ℤ)) 0
    (mapped_resolution_bounded R f M F d hF) (by infer_instance)
    (fun i => (hfinitefree i).1) (fun i => (hfinitefree i).2) ⟨eDerived.symm⟩

end

/-! ### Unique factorization -/

section

universe u v

open TensorProduct

private lemma isPrincipal_of_invertible_of_pic_subsingleton
    {R : Type*} [CommRing R] [IsDomain R] (I : Ideal R) [Module.Invertible R I]
    [Subsingleton (CommRing.Pic R)] : I.IsPrincipal := by
  apply (Submodule.rank_le_one_iff_isPrincipal I).mp
  calc
    Module.rank R I ≤ Module.rank R R :=
      (Submodule.subtype I).rank_le_of_injective (Submodule.injective_subtype I)
    _ = 1 := Module.rank_self R

private lemma uniqueFactorizationMonoid_of_ringKrullDim_eq_zero
    {R : Type*} [CommRing R] [IsDomain R]
    (h : ringKrullDim R = 0) : UniqueFactorizationMonoid R := by
  have : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr h
  let : Field R := (Ring.KrullDimLE.isField_of_isDomain (R := R)).toField
  infer_instance

private lemma prime_of_isDomain_quotient {R : Type*} [CommRing R] (x : R)
    (hx : x ≠ 0) [IsDomain (R ⧸ Ideal.span {x})] : Prime x :=
  (Ideal.span_singleton_prime hx).mp
    ((Ideal.Quotient.isDomain_iff_prime (I := Ideal.span {x})).mp inferInstance)

private lemma free_ideal_of_isPrincipal_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    (I : Ideal R) (hI : I.IsPrincipal) (hne : I ≠ ⊥) : Module.Free R I := by
  let g := Submodule.IsPrincipal.generator I
  have hg : g ≠ 0 := by
    intro hz
    apply hne
    have hspan := Submodule.IsPrincipal.span_singleton_generator I
    simpa [g, hz] using hspan.symm
  exact Module.Free.of_equiv
    (LinearEquiv.toSpanNonzeroSingleton R R g hg ≪≫ₗ
      LinearEquiv.ofEq _ _ (Submodule.IsPrincipal.span_singleton_generator I))

/-- The extension of an ideal to a localization at a prime is its localized module. -/
private noncomputable def map_ideal_equiv_localizedModule {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsPrime] (I : Ideal R) :
    I.map (algebraMap R (Localization.AtPrime P)) ≃ₗ[Localization.AtPrime P]
      LocalizedModule P.primeCompl I :=
  LinearEquiv.ofEq _ _ (Ideal.localized'_eq_map _ P.primeCompl I).symm ≪≫ₗ
    I.localizedEquiv P.primeCompl

private lemma projective_ideal_of_locally_principal {R : Type*} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (I : Ideal R) (hne : I ≠ ⊥)
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      (I.map (algebraMap R (Localization.AtPrime P))).IsPrincipal) :
    Module.Projective R I := by
  have : Module.FinitePresentation R I := Module.finitePresentation_of_finite R I
  apply Module.projective_of_localization_maximal
  intro P _
  let A := Localization.AtPrime P
  let : IsDomain A := IsLocalization.isDomain_of_atPrime A P
  let J := I.map (algebraMap R A)
  have hJ : J ≠ ⊥ := by
    simpa [J, Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective R A)] using hne
  have hfree : Module.Free A J := free_ideal_of_isPrincipal_ne_bot J (h P) hJ
  let : Module.Free A (LocalizedModule P.primeCompl I) :=
    Module.Free.of_equiv (map_ideal_equiv_localizedModule P I)
  infer_instance

private lemma invertible_of_projective_nonzero_ideal {R : Type u} [CommRing R]
    [IsDomain R] [IsNoetherianRing R] (I : Ideal R) (hne : I ≠ ⊥)
    [Module.Projective R I] : Module.Invertible R I := by
  let P : Ideal R := ⊥
  let : P.IsPrime := inferInstance
  let A := Localization.AtPrime P
  have htop : I.map (algebraMap R A) = ⊤ := by
    obtain ⟨x, hxI, hx0⟩ := I.ne_bot_iff.mp hne
    apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hxI)
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (S := A) (I := P) x).mpr
      (by simpa [P] using hx0)
  let e : LocalizedModule P.primeCompl I ≃ₗ[A] A :=
    (map_ideal_equiv_localizedModule P I).symm ≪≫ₗ LinearEquiv.ofEq _ _ htop ≪≫ₗ
      Submodule.topEquiv
  have hgeneric : Module.rankAtStalk I (⟨P, inferInstance⟩ : PrimeSpectrum R) = 1 := by
    show Module.finrank A (LocalizedModule P.primeCompl I) = 1
    rw [e.finrank_eq]
    exact Module.finrank_self A
  have hrank : Module.rankAtStalk I = Function.const (PrimeSpectrum R) 1 := by
    funext q
    have hle : (⟨P, inferInstance⟩ : PrimeSpectrum R) ≤ q := bot_le
    exact (Module.rankAtStalk_eq_of_le_of_finite_of_flat I hle).symm.trans hgeneric
  exact invertible_of_finite_projective_rankAtStalk_one hrank

private lemma uniqueFactorizationMonoid_of_locally_ufd_of_pic_subsingleton
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Subsingleton (CommRing.Pic R)]
    (h : ∀ (P : Ideal R) [P.IsMaximal],
      UniqueFactorizationMonoid (Localization.AtPrime P)) :
    UniqueFactorizationMonoid R := by
  apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
  intro p hp hph
  have hne : p ≠ ⊥ := p.ne_bot_of_height_eq_one hph
  have hloc : ∀ (P : Ideal R) [P.IsMaximal],
      (p.map (algebraMap R (Localization.AtPrime P))).IsPrincipal := by
    intro P hP
    let A := Localization.AtPrime P
    by_cases hpP : p ≤ P
    · let : (p.map (algebraMap R A)).IsPrime :=
        Ideal.isPrime_map_of_isLocalizationAtPrime P hpP
      have hd : Disjoint (P.primeCompl : Set R) (p : Set R) := by
        simpa [Ideal.primeCompl, ← le_compl_iff_disjoint_left] using hpP
      have hh : (p.map (algebraMap R A)).height = 1 :=
        (IsLocalization.height_map_of_disjoint P.primeCompl p hd).trans hph
      let : UniqueFactorizationMonoid A := h P
      exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hh
    · rw [IsLocalization.AtPrime.map_eq_top_of_not_le (S := A) hpP]
      infer_instance
  let : Module.Projective R p := projective_ideal_of_locally_principal p hne hloc
  let : Module.Invertible R p := invertible_of_projective_nonzero_ideal p hne
  exact isPrincipal_of_invertible_of_pic_subsingleton p

/-- **A Noetherian domain which is locally a unique factorization domain and has trivial Picard
group is a unique factorization domain.** Each height-one prime is locally principal, hence an
invertible module, hence principal. -/
@[ega "IV 21.7.6" "Affine integral case"]
public alias _root_.UniqueFactorizationMonoid.of_localization_maximal_of_pic_subsingleton := uniqueFactorizationMonoid_of_locally_ufd_of_pic_subsingleton

private lemma exists_prime_parameter (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R ≠ 0) :
    ∃ x : R, x ∈ IsLocalRing.maximalIdeal R ∧
      x ∉ IsLocalRing.maximalIdeal R ^ 2 ∧ Prime x := by
  let : IsDomain R := IsRegularLocalRing.isDomain R
  have hlt := IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hdim
  obtain ⟨x, hx, hx2⟩ : ∃ x : R,
      x ∈ IsLocalRing.maximalIdeal R ∧ x ∉ IsLocalRing.maximalIdeal R ^ 2 := by
    by_contra h
    push Not at h
    exact hlt.ne (le_antisymm hlt.le h)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx2 (Ideal.zero_mem _)
  have := (quotient_isRegularLocalRing R x hx hx2).1
  let : IsDomain (R ⧸ Ideal.span {x}) :=
    IsRegularLocalRing.isDomain _
  exact ⟨x, hx, hx2, prime_of_isDomain_quotient x hx0⟩

@[ega "IV 21.11.1", sga "2 XI 3.13", sga "6 X 7.8" "partial", sga "7 VIII 6.5.1" "special case"]
private lemma uniqueFactorizationMonoid_regularLocal_dim (n : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      ringKrullDim R = (n : WithBot ℕ∞) → UniqueFactorizationMonoid R := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro R hR hreg hdim
    let : IsDomain R := IsRegularLocalRing.isDomain R
    by_cases hn : n = 0
    · subst n
      exact uniqueFactorizationMonoid_of_ringKrullDim_eq_zero (by simpa using hdim)
    · have hnonzero : ringKrullDim R ≠ 0 := by
        rw [hdim]
        simpa using hn
      obtain ⟨x, hxmem, hxout, hxprime⟩ := exists_prime_parameter R hnonzero
      let A := Localization.Away x
      have : IsRegularRing R :=
        ((IsLocalRing.isRegularRing_tfae (R := R)).out 1 3).mp hreg
      have : IsDomain A := IsLocalization.Away.isDomain A hxprime.ne_zero
      have : IsNoetherianRing A :=
        IsLocalization.isNoetherianRing (Submonoid.powers x) A inferInstance
      have : Subsingleton (CommRing.Pic A) :=
        pic_subsingleton_localization_away R x
      have hlocal : ∀ (P : Ideal A) [P.IsMaximal],
          UniqueFactorizationMonoid (Localization.AtPrime P) := by
        intro P hP
        let q : Ideal R := P.comap (algebraMap R A)
        let : q.IsPrime := inferInstance
        have hxnotq : x ∉ q := by
          intro h
          have hxp : algebraMap R A x ∈ P := h
          exact hP.ne_top (P.eq_top_of_isUnit_mem hxp
            (IsLocalization.Away.algebraMap_isUnit x))
        have hqlt : q < IsLocalRing.maximalIdeal R :=
          (IsLocalRing.le_maximalIdeal_of_isPrime q).lt_of_ne fun heq => hxnotq (heq ▸ hxmem)
        have hdlt : q.height < ringKrullDim R := by
          rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
          exact_mod_cast Ideal.height_strict_mono_of_isPrime_of_isPrime hqlt
        let B := Localization.AtPrime q
        have : IsRegularLocalRing B := IsRegularRing.isRegularLocalRing_localization q
        let m := (IsLocalRing.maximalIdeal B).spanFinrank
        have hmEq : ringKrullDim B = (m : WithBot ℕ∞) := by
          simpa [m] using (IsRegularLocalRing.spanFinrank_maximalIdeal (R := B)).symm
        have hmn : m < n := by
          have hd : (m : WithBot ℕ∞) < (n : WithBot ℕ∞) := by
            rw [← hmEq, IsLocalization.AtPrime.ringKrullDim_eq_height q B, ← hdim]
            exact hdlt
          exact_mod_cast hd
        have : UniqueFactorizationMonoid B := ih m hmn B hmEq
        have : IsLocalization.AtPrime (Localization.AtPrime P) q :=
          IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
            (Submonoid.powers x) (Localization.AtPrime P) P
        let e := (IsLocalization.algEquiv q.primeCompl B
          (Localization.AtPrime P)).toRingEquiv
        exact e.toMulEquiv.uniqueFactorizationMonoid inferInstance
      have : UniqueFactorizationMonoid A :=
        uniqueFactorizationMonoid_of_locally_ufd_of_pic_subsingleton hlocal
      exact (UniqueFactorizationMonoid.iff_localizationAway_of_prime hxprime).mpr
        inferInstance

/-- **Stacks 0AG0.** A regular local ring is a unique factorization domain. -/
@[stacks 0AG0, sga "2 XI 3.13", sga "6 X 7.8" "more general", sga "7 VIII 6.5.1" "special case"]
public theorem uniqueFactorizationMonoid
    (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    UniqueFactorizationMonoid R := by
  let n := (IsLocalRing.maximalIdeal R).spanFinrank
  have hdim : ringKrullDim R = (n : WithBot ℕ∞) := by
    simpa [n] using (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  exact uniqueFactorizationMonoid_regularLocal_dim n R hdim

end

end IsRegularLocalRing
