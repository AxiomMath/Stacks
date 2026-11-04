module

public import Mathlib.Algebra.Field.Shrink
public import StacksFrontier.RingTheory.CompleteIntersection.FieldGlobalToRingMap
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Module.Projective.Invertible
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.DedekindComparison
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingModuleComparison
public import StacksFrontier.Homology.DerivedCategory.Monoidal.Invertible
public import StacksFrontier.RingTheory.Artinian.FiniteType
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.DerivedCoextensionIsDualizing
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinCriteria
public import StacksFrontier.RingTheory.Dualizing.GorensteinLocalCompleteIntersection
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext
import StacksFrontier.LinearAlgebra.TensorProduct.BaseChangeCancellation
import StacksFrontier.RingTheory.Dualizing.Complex
import StacksFrontier.RingTheory.Dualizing.RelativeComposition

/-!
# Dualizing modules of zero-dimensional global complete intersections

Let `k` be a field and let `B` be a global complete intersection over `k` of dimension `0`, that
is `B = k[x_1, …, x_n]/(f_1, …, f_n)` with `dim B = 0`. Then the relative dualizing module
`ω_{B/k}` of `k → B` is an invertible `B`-module.

## Main results

* `Stacks.Discriminant.dualizingModule_invertible_of_isGlobalCompleteIntersection` —
  **[Stacks, Tag 0DWL]**, the relative dualizing module of a zero-dimensional global complete
  intersection over a field is invertible.
* `Stacks.Discriminant.isGorensteinRing_of_invertible_dual` — a finite algebra over a field
  whose dual is invertible is Gorenstein, the converse of
  `Stacks.Discriminant.invertible_dual_of_isGorensteinRing`.

## Implementation notes

The dimension hypothesis makes `B` finite over `k`
(`Algebra.FiniteType.krullDimLE_zero_tfae`, which is Noether normalization in the form the
source cites it), so the identity factorization `k → B → B` of
`Stacks.Discriminant.selfFactorization` is a finite-open factorization and
`Stacks.Discriminant.selfFactorizationDualEquiv` identifies its dualizing module with
`Hom_k(B, k)`. The statement is made for an arbitrary finite-open factorization `F`, and
`Stacks.Discriminant.dualizingModuleEquiv` [Stacks, Tag 0BT1] transports the conclusion to it.

What is proved about `Hom_k(B, k)` is that it is the degree-zero cohomology of the dualizing
complex `RHom_k(B, k)` of `B` [Stacks, Tag 0AX0], which is invertible in `D(B)` because `B` is
Gorenstein [Stacks, Tag 0DW9 (1)(a)]; `B` is Gorenstein because `k → B` is a local complete
intersection homomorphism out of a field [Stacks, Tag 0DWA]. Invertibility of a single module
is read off from invertibility of the complex it sits in through
`DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit`: the complex is locally a
shifted copy of the ring, the shift is zero because the module is faithful, and a finite
projective module of rank one everywhere is invertible.

The derived input is only available when the ring and the module universe agree, so `k` is
replaced by `Shrink.{v} k`, which is legitimate because `k` injects into `B`.

The dimension hypothesis is `ringKrullDim B = 0` rather than `Ring.KrullDimLE 0 B`: it is the
source's `dim B = 0`, and it rules out the zero ring, whose Krull dimension is `⊥`.

## References

* [Stacks Project, Tag 0DWL](https://stacks.math.columbia.edu/tag/0DWL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-- A ring of Krull dimension `0` is nontrivial. -/
private theorem nontrivial_of_ringKrullDim_eq_zero {B : Type v} [CommRing B]
    (hdim : ringKrullDim B = 0) : Nontrivial B := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
  exact absurd hdim (by simp)

/-- A zero-dimensional global complete intersection over a field is finite over that field. This
is the form in which the source invokes Noether normalization. -/
private theorem finite_of_ringKrullDim_eq_zero_isGlobalCompleteIntersection
    {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
    (hB : IsGlobalCompleteIntersection k B) (hdim : ringKrullDim B = 0) :
    Module.Finite k B := by
  let : Algebra.FiniteType k B := hB.finiteType k
  have hdimLE : Ring.KrullDimLE 0 B := by
    have := nontrivial_of_ringKrullDim_eq_zero hdim
    exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hdim
  exact (Algebra.FiniteType.krullDimLE_zero_tfae k B).out 1 5 |>.mp hdimLE

/-- A field is a Gorenstein ring. -/
private theorem field_isGorensteinRing (k : Type u) [Field k] :
    Dualizing.IsGorensteinRing k :=
  Dualizing.IsRegularRing.isGorensteinRing k

/-- The residue field of a field at its zero ideal is the field itself. -/
private noncomputable def residueFieldEquivOfField (k : Type u) [Field k] :
    (⊥ : Ideal k).ResidueField ≃ₐ[k] k := by
  let M := (⊥ : Ideal k).primeCompl
  letI : IsLocalization M k := IsLocalization.self (by
    intro x hx
    apply isUnit_iff_ne_zero.mpr
    intro hx0
    apply hx
    simp [hx0])
  let L := Localization.AtPrime (⊥ : Ideal k)
  let eL : L ≃ₐ[k] k := IsLocalization.algEquiv M L k
  let eQ : IsLocalRing.ResidueField k ≃ₐ[k] k :=
    (Ideal.quotientEquivAlgOfEq k (IsLocalRing.maximalIdeal_eq_bot (R := k))).trans
      (AlgEquiv.quotientBot k k)
  change IsLocalRing.ResidueField L ≃ₐ[k] k
  exact (IsLocalRing.ResidueField.mapAlgEquiv eL).trans eQ

/-- A nonzero global complete intersection over a field is a relative global complete
intersection over it. -/
private theorem isRelativeGlobalCompleteIntersection_of_isGlobalCompleteIntersection
    {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
    (hB : IsGlobalCompleteIntersection k B)
    [Nontrivial B] : Algebra.IsRelativeGlobalCompleteIntersection k B := by
  obtain ⟨n, c, f, e, hcn, hdim'⟩ :=
    hB.resolve_left (not_subsingleton_iff_nontrivial.mpr inferInstance)
  let P : Algebra.Presentation k B (Fin n) (Fin c) :=
    (Algebra.Presentation.naive (v := f)).ofAlgEquiv e.symm
  have : P.IsRelativeGlobalCompleteIntersection := by
    refine ⟨fun p hp hfiber => ?_⟩
    obtain rfl : p = ⊥ := (Ideal.eq_bot_or_top p).resolve_right hp.ne_top
    let eFiber : (⊥ : Ideal k).Fiber B ≃ₐ[k] B :=
      (Algebra.TensorProduct.congr (residueFieldEquivOfField k)
        (AlgEquiv.refl (R := k) (A₁ := B))).trans
        (Algebra.TensorProduct.lid k B)
    rw [ringKrullDim_eq_of_ringEquiv eFiber.toRingEquiv, hdim']
    norm_cast
    rw [Nat.card_fin, Nat.card_fin]
    omega
  exact Algebra.IsRelativeGlobalCompleteIntersection.of_presentation P

/-- A relative global complete intersection is a local complete intersection homomorphism. -/
private theorem isLocalCompleteIntersection_algebraMap
    {k : Type u} {B : Type v} [CommRing k] [CommRing B] [Algebra k B]
    (hB : Algebra.IsRelativeGlobalCompleteIntersection k B) :
    RingHom.IsLocalCompleteIntersection (algebraMap k B) := by
  obtain ⟨n, c, P, hP⟩ := hB.out
  have : Algebra.FinitePresentation k B := P.finitePresentation_of_isFinite
  rw [RingHom.IsLocalCompleteIntersection, toAlgebra_algebraMap]
  refine ⟨RingHom.finiteType_algebraMap.mpr inferInstance,
    n, MvPolynomial.aeval P.val, P.aeval_val_surjective, ?_⟩
  show Ideal.IsKoszulRegular (RingHom.ker (MvPolynomial.aeval (R := k) P.val))
  rw [← P.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker]
  exact isKoszulRegularIdeal_span_range P.relation
    (RingHom.isKoszulRegular_relation_of_isRelativeGlobalCompleteIntersection P hP)

/-- A field is injective as a module over itself. -/
private theorem field_injective_self (k : Type u) [Field k] :
    Injective (ModuleCat.of k k) := by
  have : Module.Injective k k := Module.injective_of_isSemisimpleRing k _
  exact Module.injective_object_of_injective_module k k

/-- Over a field `k`, the derived Hom along `k → B` of `k` placed in degree zero is the
coextension of scalars of `k`, placed in degree zero. -/
private noncomputable def derivedHom_single_coextendScalars_iso
    {k B : Type u} [Field k] [CommRing B] [Algebra k B] :
    (Dualizing.derivedHom.{u, u} (algebraMap k B)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        ((ModuleCat.coextendScalars (algebraMap k B)).obj (ModuleCat.of k k)) := by
  let f := algebraMap k B
  let I := (CochainComplex.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)
  let F := (ModuleCat.coextendScalars f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso (ModuleCat.{u} k) (ComplexShape.up ℤ)
  let RF := Dualizing.derivedHom.{u, u} f
  let α := F.totalRightDerivedUnit DerivedCategory.Qh W
  have hI : I.IsKInjective := by
    let : I.IsStrictlyGE 0 := by dsimp [I]; infer_instance
    let : ∀ i, Injective (I.X i) := by
      intro i
      by_cases hi : i = 0
      · subst i
        let : Module.Injective k k := Module.injective_of_isSemisimpleRing k _
        exact Module.injective_object_of_injective_module k _
      · change Injective (((HomologicalComplex.single (ModuleCat k)
          (ComplexShape.up ℤ) 0).obj (ModuleCat.of k k)).X i)
        exact (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 (ModuleCat.of k k) i hi).injective
    exact CochainComplex.isKInjective_of_injective I 0
  have hA : ∀ K : CochainComplex (ModuleCat.{u} k) ℤ,
      ∃ (J : CochainComplex (ModuleCat.{u} k) ℤ) (g : K ⟶ J),
        J.IsKInjective ∧ QuasiIso g := by
    intro K
    obtain ⟨J, g, hg, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective K
    exact ⟨J, g, hJ, hg⟩
  have : IsIso (α.app
      ((HomotopyCategory.quotient (ModuleCat.{u} k) (ComplexShape.up ℤ)).obj I)) := by
    have hh := Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      F hA
    have : RF.IsRightDerivedFunctor α W := Dualizing.derivedHom_isRightDerivedFunctor f
    exact hh.2 (L := DerivedCategory.Qh) (RF := RF) (α := α) I hI
  let eα := asIso (α.app
      ((HomotopyCategory.quotient (ModuleCat.{u} k) (ComplexShape.up ℤ)).obj I))
  let eI : (HomotopyCategory.quotient (ModuleCat.{u} k) (ComplexShape.up ℤ)).obj I ≅
      (HomotopyCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k) :=
    (HomotopyCategory.singleFunctorPostcompQuotientIso (ModuleCat.{u} k) 0).app
      (ModuleCat.of k k) |>.symm
  let eInput : RF.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
        (ModuleCat.of k k)) ≅
      (DerivedCategory.Qh ⋙ RF).obj
        ((HomotopyCategory.quotient (ModuleCat.{u} k) (ComplexShape.up ℤ)).obj I) :=
    RF.mapIso ((DerivedCategory.singleFunctorIsoCompQh (ModuleCat.{u} k) 0).app
      (ModuleCat.of k k)) ≪≫
      RF.mapIso (DerivedCategory.Qh.mapIso eI.symm)
  let esource : F.obj
      ((HomotopyCategory.quotient (ModuleCat.{u} k) (ComplexShape.up ℤ)).obj I) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        ((ModuleCat.coextendScalars f).obj (ModuleCat.of k k)) := by
    dsimp [F]
    let F0 := ModuleCat.coextendScalars f
    exact DerivedCategory.Qh.mapIso
        ((F0.mapHomotopyCategory (ComplexShape.up ℤ)).mapIso eI) ≪≫
      (Functor.isoWhiskerRight
        (CategoryTheory.Functor.mapHomotopyCategorySingleFunctor F0 0) DerivedCategory.Qh).app
          (ModuleCat.of k k) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQh (ModuleCat B) 0).app
        (F0.obj (ModuleCat.of k k))).symm
  exact eInput ≪≫ eα.symm ≪≫ esource

/-- Cohomology of a derived localization away from an element, as a localized module. -/
private noncomputable def derivedAwayHomologyLinearEquiv
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{u} R))
    (f : R) (n : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away f)) n).obj
      ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap R (Localization.Away f))).functor.obj K)) ≃ₗ[Localization.Away f]
      LocalizedModule.Away f
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K) := by
  let N := (DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away f)) n).obj
    ((totalDerivedExtensionScalars.{u, u, u}
      (algebraMap R (Localization.Away f))).functor.obj K)
  let N' := (ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).obj N
  letI : Module (Localization.Away f) N' := inferInstanceAs (Module (Localization.Away f) N)
  let e : N' ≃ₗ[R] LocalizedModule.Away f
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K) :=
    ((CochainComplex.DerivedTensor.derivedExtensionScalarsAwayHomologyIso.{u, u} f n).app
      K).toLinearEquiv
  have : IsScalarTower R (Localization.Away f) N' :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact e.extendScalarsOfIsLocalization (Submonoid.powers f) (Localization.Away f)

/-- A faithful module whose single-term complex is invertible in the derived category is an
invertible module. -/
private theorem module_invertible_of_derived_single_invertible
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    (hfaith : FaithfulSMul R M)
    (hinv : letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
      MonoidalCategory.IsInvertible
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) :
    Module.Invertible R M := by
  let D := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
  have hcriterion := DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit D
  have hdata := hcriterion.2 hinv
  have hlocal : DerivedCategory.Invertible.IsLocallyShiftedUnit D := hcriterion.1.mp hinv
  let H0 := (DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).obj D
  let eH0 : H0 ≃ₗ[R] M :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app
      M).toLinearEquiv
  have hfinproj : Module.Finite R H0 ∧ Module.Projective R H0 := hdata.2.2.1 0
  let : Module.Finite R H0 := hfinproj.1
  let : Module.Projective R H0 := hfinproj.2
  let : Module.Finite R M := Module.Finite.equiv eH0
  let : Module.Projective R M := Module.Projective.of_equiv eH0
  have hfaith0 : FaithfulSMul R H0 :=
    ⟨fun hab => hfaith.eq_of_smul_eq_smul fun x => by simpa using congrArg eH0 (hab (eH0.symm x))⟩
  have hsupp0 : Module.support R H0 = Set.univ := by
    rw [Module.support_eq_zeroLocus, Module.annihilator_eq_bot.mpr hfaith0]
    simp
  have hrank : Module.rankAtStalk M = Function.const (PrimeSpectrum R) 1 := by
    funext p
    obtain ⟨f, hf, n, ⟨e⟩⟩ := hlocal p.asIdeal p.isPrime
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
    let Hloc := DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.Away f)) 0
    let j := (Hloc.mapIso e).toLinearEquiv.symm.trans
      (derivedAwayHomologyLinearEquiv D f 0)
    have hn : n = 0 := by
      by_contra hne
      have hz : Limits.IsZero (Hloc.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) n).obj
            (ModuleCat.of (Localization.Away f) (Localization.Away f)))) := by
        rcases lt_or_gt_of_ne (Ne.symm hne) with hlt | hgt
        · exact DerivedCategory.isZero_of_isGE _ n 0 hlt
        · exact DerivedCategory.isZero_of_isLE _ n 0 hgt
      have hsubSrc : Subsingleton (Hloc.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.Away f)) n).obj
            (ModuleCat.of (Localization.Away f) (Localization.Away f)))) :=
        ModuleCat.isZero_iff_subsingleton.mp hz
      have hsub : Subsingleton (LocalizedModule.Away f H0) := j.symm.injective.subsingleton
      have hpSupport : (⟨p.asIdeal, p.isPrime⟩ : PrimeSpectrum R) ∈
          Module.support R H0 := by
        simp [hsupp0]
      have hpZero : (⟨p.asIdeal, p.isPrime⟩ : PrimeSpectrum R) ∈
          PrimeSpectrum.zeroLocus ({f} : Set R) :=
        (LocalizedModule.subsingleton_iff_support_subset.mp hsub) hpSupport
      exact hf ((PrimeSpectrum.mem_zeroLocus
        (⟨p.asIdeal, p.isPrime⟩ : PrimeSpectrum R) ({f} : Set R)).mp hpZero (by simp))
    subst n
    let S := Submonoid.powers f
    obtain ⟨q, hq⟩ : ∃ q : PrimeSpectrum (Localization.Away f),
        q.comap (algebraMap R (Localization.Away f)) = p :=
      (PrimeSpectrum.localization_away_comap_range (Localization.Away f) f).symm.le hf
    show Module.rankAtStalk M p = 1
    rw [Module.rankAtStalk_eq_of_equiv eH0.symm, ← hq,
      ← Module.rankAtStalk_isBaseChange (LocalizedModule.isBaseChange S H0) q]
    show Module.rankAtStalk (LocalizedModule.Away f H0) q = 1
    have : Nontrivial (Localization.Away f) := q.nontrivial
    have hj := congrFun (Module.rankAtStalk_eq_of_equiv j) q
    have hself := congrFun (Module.rankAtStalk_eq_of_equiv
      (((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} (Localization.Away f)) 0).app
          (ModuleCat.of (Localization.Away f) (Localization.Away f))).toLinearEquiv)) q
    exact hj.symm.trans (hself.trans (congrFun Module.rankAtStalk_self q))
  exact (Module.finite_projective_rankAtStalk_one_tfae_invertible_exists_tensor_inverse.{u, u, u}
    (R := R) (M := M)).1.out 1 2 |>.mp
      (show Module.Finite R M ∧ Module.Projective R M ∧
          Module.rankAtStalk M = Function.const (PrimeSpectrum R) 1 from
        ⟨inferInstance, inferInstance, hrank⟩)

/-- The dual of a finite algebra over a field is a faithful module over the algebra. -/
private theorem faithfulSMul_dual
    {k B : Type u} [Field k] [CommRing B] [Algebra k B] [Module.Finite k B] :
    FaithfulSMul B (Module.Dual k B) := by
  have : Module.Projective k B := inferInstance
  refine ⟨?_⟩
  intro b c h
  apply sub_eq_zero.mp
  apply Module.eval_apply_injective k (V := B)
  ext φ
  have hsub : (b - c) • φ = 0 := by
    rw [sub_smul]
    exact sub_eq_zero.mpr (h φ)
  have hv := congrArg (fun ψ : Module.Dual k B => ψ 1) hsub
  simpa [algebraDualModule_smul_apply, Module.Dual.eval_apply] using hv

/-- Transport of a dual along a ring isomorphism of the base, on underlying functions. -/
private def dualMapOfRingEquiv
    {K B : Type v} {k : Type u} [CommRing K] [CommRing k] [CommRing B]
    [Algebra K k] [Algebra k B] [Algebra K B] [IsScalarTower K k B]
    (e : K ≃+* k) (hcomp : ∀ x : K,
      algebraMap K B x = algebraMap k B (e x)) (φ : Module.Dual K B) :
    Module.Dual k B := {
    toFun := fun x => e (φ x)
    map_add' x y := by simp
    map_smul' := by
      intro a x
      have h : (a : k) • x = (e.symm a : K) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, hcomp (e.symm a)]
        simp
      calc
        e (φ (a • x)) = e (φ ((e.symm a) • x)) := by rw [h]
        _ = e ((e.symm a) • φ x) := by rw [map_smul]
        _ = a • e (φ x) := by simp
  }

/-- The inverse transport of a dual along a ring isomorphism of the base. -/
private def invDualMapOfRingEquiv
    {K B : Type v} {k : Type u} [CommRing K] [CommRing k] [CommRing B]
    [Algebra K k] [Algebra k B] [Algebra K B] [IsScalarTower K k B]
    (e : K ≃+* k) (hcomp : ∀ x : K,
      algebraMap K B x = algebraMap k B (e x)) (ψ : Module.Dual k B) :
    Module.Dual K B := {
    toFun := fun x => e.symm (ψ x)
    map_add' x y := by simp
    map_smul' := by
      intro a x
      have h : (a : K) • x = (e a : k) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, hcomp a]
      calc
        e.symm (ψ (a • x)) = e.symm (ψ ((e a) • x)) := by rw [h]
        _ = e.symm ((e a) • ψ x) := by rw [map_smul]
        _ = a • e.symm (ψ x) := by simp
  }

/-- Transport of a dual along a ring isomorphism of the base is linear over the algebra. -/
private def dualFwdLinearOfRingEquiv
    {K B : Type v} {k : Type u} [CommRing K] [CommRing k] [CommRing B]
    [Algebra K k] [Algebra k B] [Algebra K B] [IsScalarTower K k B]
    [Module B (Module.Dual K B)] [Module B (Module.Dual k B)]
    (e : K ≃+* k) (hcomp : ∀ x : K,
      algebraMap K B x = algebraMap k B (e x))
    (hsmulK : ∀ (b x : B) (φ : Module.Dual K B), (b • φ) x = φ (b * x))
    (hsmulk : ∀ (b x : B) (φ : Module.Dual k B), (b • φ) x = φ (b * x)) :
    Module.Dual K B →ₗ[B] Module.Dual k B := by
  let fAdd : Module.Dual K B →+ Module.Dual k B :=
    AddMonoidHom.mk' (dualMapOfRingEquiv e hcomp)
      (by intro φ ψ; ext x; simp [dualMapOfRingEquiv])
  exact LinearMap.mk fAdd (by
    intro b φ
    ext x
    change e ((b • φ) x) = (b • dualMapOfRingEquiv e hcomp φ) x
    rw [hsmulK, hsmulk]
    rfl)

/-- The inverse transport of a dual along a ring isomorphism of the base is linear. -/
private def dualInvLinearOfRingEquiv
    {K B : Type v} {k : Type u} [CommRing K] [CommRing k] [CommRing B]
    [Algebra K k] [Algebra k B] [Algebra K B] [IsScalarTower K k B]
    [Module B (Module.Dual K B)] [Module B (Module.Dual k B)]
    (e : K ≃+* k) (hcomp : ∀ x : K,
      algebraMap K B x = algebraMap k B (e x))
    (hsmulK : ∀ (b x : B) (φ : Module.Dual K B), (b • φ) x = φ (b * x))
    (hsmulk : ∀ (b x : B) (φ : Module.Dual k B), (b • φ) x = φ (b * x)) :
    Module.Dual k B →ₗ[B] Module.Dual K B := by
  let fAdd : Module.Dual k B →+ Module.Dual K B :=
    AddMonoidHom.mk' (invDualMapOfRingEquiv e hcomp)
      (by intro φ ψ; ext x; simp [invDualMapOfRingEquiv])
  exact LinearMap.mk fAdd (by
    intro b φ
    ext x
    change e.symm ((b • φ) x) = (b • invDualMapOfRingEquiv e hcomp φ) x
    rw [hsmulk, hsmulK]
    rfl)

/-- A ring isomorphism of the base induces an isomorphism of the duals, linear over the
algebra. -/
private noncomputable def dualEquivOfRingEquiv
    {K B : Type v} {k : Type u} [CommRing K] [CommRing k] [CommRing B]
    [Algebra K k] [Algebra k B] [Algebra K B] [IsScalarTower K k B]
    [Module B (Module.Dual K B)] [Module B (Module.Dual k B)]
    (e : K ≃+* k) (hcomp : ∀ x : K,
      algebraMap K B x = algebraMap k B (e x))
    (hsmulK : ∀ (b x : B) (φ : Module.Dual K B), (b • φ) x = φ (b * x))
    (hsmulk : ∀ (b x : B) (φ : Module.Dual k B), (b • φ) x = φ (b * x)) :
    Module.Dual K B ≃ₗ[B] Module.Dual k B := by
  let fwd := dualFwdLinearOfRingEquiv e hcomp hsmulK hsmulk
  let inv := dualInvLinearOfRingEquiv e hcomp hsmulK hsmulk
  exact {
    toFun := fwd
    invFun := inv
    left_inv := by
      intro φ
      ext x
      simp [fwd, inv, dualFwdLinearOfRingEquiv, dualInvLinearOfRingEquiv,
        dualMapOfRingEquiv, invDualMapOfRingEquiv]
    right_inv := by
      intro φ
      ext x
      simp [fwd, inv, dualFwdLinearOfRingEquiv, dualInvLinearOfRingEquiv,
        dualMapOfRingEquiv, invDualMapOfRingEquiv]
    map_add' := by intro φ ψ; ext x; simp [fwd]
    map_smul' := by
      intro b φ
      ext x
      simp [fwd]
  }

/-- Coextension of scalars along `k → B` applied to `k` is the dual `Hom_k(B, k)`, as a
`B`-module. -/
private noncomputable def coextendScalars_dual_equiv
    {K B : Type v} [Field K] [CommRing B] [Algebra K B]
    [Module B (Module.Dual K B)]
    (hsmul : ∀ (b x : B) (φ : Module.Dual K B), (b • φ) x = φ (b * x)) :
    ((ModuleCat.coextendScalars (algebraMap K B)).obj (ModuleCat.of K K)) ≃ₗ[B]
      Module.Dual K B := by
  let f := algebraMap K B
  let E : ModuleCat K := ModuleCat.of K K
  let D : ModuleCat K := (ModuleCat.restrictScalars f).obj (ModuleCat.of B B)
  let eD : D ≃ₗ[K] B := {
    toFun := id
    invFun := id
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun a x =>
      (ModuleCat.restrictScalars.smul_def f a x).trans
        ((smul_eq_mul (α := B) (f a) x).trans (Algebra.smul_def (A := B) a x).symm) }
  let eE : E ≃ₗ[K] K := by
    change K ≃ₗ[K] K
    exact LinearEquiv.refl K K
  let eHom : (D →ₗ[K] E) ≃ₗ[K] (B →ₗ[K] K) := eD.arrowCongr eE
  let gMap : ↑((ModuleCat.coextendScalars f).obj E) → Module.Dual K B :=
    fun g => eHom (ModuleCat.CoextendScalars.equiv f E g)
  let fAdd : ((ModuleCat.coextendScalars f).obj E) →+ Module.Dual K B :=
    AddMonoidHom.mk' gMap (by intro x y; ext z; simp [gMap, eHom])
  let toDual : ((ModuleCat.coextendScalars f).obj E) →ₗ[B] Module.Dual K B :=
    LinearMap.mk fAdd (by
      intro b g
      ext x
      rw [hsmul]
      change eE (ModuleCat.CoextendScalars.equiv f E g (x * b))
        = eE (ModuleCat.CoextendScalars.equiv f E g (b * x))
      rw [mul_comm])
  have hbij : Function.Bijective
      (fun g => eHom (ModuleCat.CoextendScalars.equiv f E g)) :=
    eHom.bijective.comp (ModuleCat.CoextendScalars.equiv f E).bijective
  have hbij' : Function.Bijective toDual := by
    simpa [toDual, fAdd, gMap] using hbij
  exact LinearEquiv.ofBijective toDual hbij'

/-- Invertibility of an object of a monoidal category transfers along an isomorphism. -/
private theorem isInvertible_of_iso {C : Type*} [Category C] [MonoidalCategory C] {X Y : C}
    (e : X ≅ Y) (h : MonoidalCategory.IsInvertible X) : MonoidalCategory.IsInvertible Y := by
  obtain ⟨h⟩ := h
  exact ⟨{
    inv := h.inv
    isoLeft := tensorIso e.symm (Iso.refl h.inv) ≪≫ h.isoLeft
    isoRight := tensorIso (Iso.refl h.inv) e.symm ≪≫ h.isoRight }⟩

/-- A Noetherian algebra `B`, finite over a field `K`, is Gorenstein iff the coextension of
scalars of `K` to `B`, placed in degree zero, is invertible in `D(B)`. -/
private theorem isGorensteinRing_iff_isInvertible_single_coextendScalars
    {K B : Type v} [Field K] [CommRing B] [Algebra K B] [Module.Finite K B] [IsNoetherianRing B] :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
    Dualizing.IsGorensteinRing B ↔ MonoidalCategory.IsInvertible
      ((DerivedCategory.singleFunctor (ModuleCat.{v} B) 0).obj
        ((ModuleCat.coextendScalars (algebraMap K B)).obj (ModuleCat.of K K))) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory B).choose
  have hK : Dualizing.IsDualizingComplex
      ((DerivedCategory.singleFunctor (ModuleCat.{v} K) 0).obj (ModuleCat.of K K)) :=
    Dualizing.IsRegularLocalRing.isGorensteinLocalRing K
  have hDB := Dualizing.isDualizingComplex_derivedHom_of_finite (algebraMap K B)
    (RingHom.finite_algebraMap.mpr inferInstance) _ hK
  rw [Dualizing.isGorensteinRing_iff_isInvertible_canonical _ hDB]
  let eCo := derivedHom_single_coextendScalars_iso (k := K) (B := B)
  exact ⟨isInvertible_of_iso eCo, isInvertible_of_iso eCo.symm⟩

/-- A finite algebra `B` over a field `k` is also finite over a field `K` in the universe of `B`
for which the coextension of scalars of `K` to `B` is the dual `Hom_k(B, k)`. -/
private theorem exists_field_coextendScalars_equiv_dual
    {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B] [Module.Finite k B]
    [Nontrivial B] :
    ∃ (K : Type v) (_ : Field K) (_ : Algebra K B), Module.Finite K B ∧
      Nonempty (((ModuleCat.coextendScalars (algebraMap K B)).obj (ModuleCat.of K K)) ≃ₗ[B]
        Module.Dual K B) ∧ Nonempty (Module.Dual K B ≃ₗ[B] Module.Dual k B) := by
  let : Small.{v} k := small_of_injective (FaithfulSMul.algebraMap_injective k B)
  let K := Shrink.{v} k
  let e : K ≃+* k := Shrink.ringEquiv k
  let : Algebra K k := e.toRingHom.toAlgebra
  let : Algebra K B := ((algebraMap k B).comp e.toRingHom).toAlgebra
  let : IsScalarTower K k B := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have : Module.Finite K B := by
    let : Module.Finite K k := e.finite
    exact Module.Finite.trans k B
  exact ⟨K, inferInstance, inferInstance, inferInstance,
    ⟨coextendScalars_dual_equiv (K := K) (B := B)
      (fun b x φ => algebraDualModule_smul_apply K B b x φ)⟩,
    ⟨dualEquivOfRingEquiv (K := K) (k := k) (B := B) e (fun x => rfl)
      (fun b x φ => algebraDualModule_smul_apply K B b x φ)
      (fun b x φ => algebraDualModule_smul_apply k B b x φ)⟩⟩

/-- The dual `Hom_k(B, k)` of a finite Gorenstein algebra over a field is an invertible
`B`-module. -/
theorem invertible_dual_of_isGorensteinRing
    {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
    [Module.Finite k B] [Nontrivial B] [IsNoetherianRing B]
    (hG : Dualizing.IsGorensteinRing B) :
    Module.Invertible B (Module.Dual k B) := by
  obtain ⟨K, _, _, _, ⟨q⟩, ⟨eDual⟩⟩ :=
    exists_field_coextendScalars_equiv_dual (k := k) (B := B)
  have hSingleInv := isGorensteinRing_iff_isInvertible_single_coextendScalars (K := K) (B := B)
    |>.mp hG
  have hfaithC : FaithfulSMul B ((ModuleCat.coextendScalars (algebraMap K B)).obj
      (ModuleCat.of K K)) := by
    refine ⟨fun {b c} hbc => (faithfulSMul_dual (k := K) (B := B)).eq_of_smul_eq_smul fun φ => ?_⟩
    simpa only [map_smul, q.apply_symm_apply] using congrArg q (hbc (q.symm φ))
  have : Module.Invertible B ((ModuleCat.coextendScalars (algebraMap K B)).obj
      (ModuleCat.of K K)) :=
    module_invertible_of_derived_single_invertible _ hfaithC hSingleInv
  have : Module.Invertible B (Module.Dual K B) := Module.Invertible.congr q
  exact Module.Invertible.congr eDual

/-- An invertible module placed in degree zero is an invertible object of the derived category.
-/
theorem isInvertible_single_of_invertible {R : Type u} [CommRing R] (M : ModuleCat.{u} R)
    [Module.Invertible R M] :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
    MonoidalCategory.IsInvertible
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  let := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory R).choose
  refine ((DerivedCategory.Invertible.isInvertible_iff_locallyShiftedUnit _).1).mpr ?_
  intro p hp
  obtain ⟨s, hs, hfree⟩ := Module.Invertible.exists_finset_free_localization (R := R) (M := M)
  obtain ⟨r, hrs, hrp⟩ : ∃ r ∈ s, r ∉ p := by
    by_contra! h
    exact hp.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr h))
  refine ⟨r, hrp, 0, ?_⟩
  let Rr := Localization.Away r
  have hflat : (algebraMap R Rr).Flat := by
    rw [RingHom.flat_algebraMap_iff]; infer_instance
  have := hfree r hrs
  let eB : Rr ⊗[R] M ≃ₗ[Rr] LocalizedModule.Away r M :=
    (IsLocalizedModule.isBaseChange (Submonoid.powers r) Rr
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M)).equiv
  have : Module.Free Rr (Rr ⊗[R] M) := Module.Free.of_equiv eB.symm
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := Rr) (M := Rr ⊗[R] M)).mp this
  exact ⟨Dualizing.totalDerivedExtensionScalarsSingleIsoOfFlat (algebraMap R Rr) hflat M ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} Rr) 0).mapIso
      (Stacks.TensorProductPushout.extendScalarsObjIso M ≪≫ LinearEquiv.toModuleIso e)⟩

/-- **A finite algebra over a field with invertible dual is Gorenstein.** For a field `k` and a
nonzero finite `k`-algebra `B`, if `Hom_k(B, k)` is an invertible `B`-module then `B` is a
Gorenstein ring.

This is the converse of `Stacks.Discriminant.invertible_dual_of_isGorensteinRing`: the dual is
the degree-zero cohomology of the dualizing complex `RHom_k(B, k)` of `B` [Stacks, Tag 0AX0], an
invertible module in degree zero is invertible in `D(B)`, and a dualizing complex is invertible
only over a Gorenstein ring [Stacks, Tag 0DW9 (1)(a)]. -/
theorem isGorensteinRing_of_invertible_dual
    {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
    [Module.Finite k B] [Nontrivial B] [IsNoetherianRing B]
    [Module.Invertible B (Module.Dual k B)] :
    Dualizing.IsGorensteinRing B := by
  obtain ⟨K, _, _, _, ⟨q⟩, ⟨eDual⟩⟩ :=
    exists_field_coextendScalars_equiv_dual (k := k) (B := B)
  have : Module.Invertible B ((ModuleCat.coextendScalars (algebraMap K B)).obj
      (ModuleCat.of K K)) := Module.Invertible.congr (q.trans eDual).symm
  exact (isGorensteinRing_iff_isInvertible_single_coextendScalars (K := K) (B := B)).mpr
    (isInvertible_single_of_invertible _)

/-- **Stacks Project, Tag 0DWL.** Let `k` be a field and let `B` be a global complete
intersection over `k` of dimension `0`. Then the relative dualizing module `ω_{B/k}` is an
invertible `B`-module.

The dualizing module is computed from an arbitrary finite-open factorization of `k → B`; the
choice is immaterial by `Stacks.Discriminant.dualizingModuleEquiv`. -/
@[stacks 0DWL]
theorem dualizingModule_invertible_of_isGlobalCompleteIntersection
    {k : Type u} {B : Type v} [Field k] [CommRing B] [Algebra k B]
    (F : FiniteOpenFactorization.{u, v, w} k B)
    (hB : IsGlobalCompleteIntersection k B) (hdim : ringKrullDim B = 0) :
    Module.Invertible B (dualizingModule F) := by
  have : Module.Finite k B :=
    finite_of_ringKrullDim_eq_zero_isGlobalCompleteIntersection hB hdim
  have := nontrivial_of_ringKrullDim_eq_zero hdim
  have : Algebra.FiniteType k B := hB.finiteType k
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let : Algebra.IsRelativeGlobalCompleteIntersection k B :=
    isRelativeGlobalCompleteIntersection_of_isGlobalCompleteIntersection hB
  have hG : Dualizing.IsGorensteinRing B :=
    Dualizing.isGorensteinRing_of_isLocalCompleteIntersection (algebraMap k B)
      (isLocalCompleteIntersection_algebraMap (k := k) (B := B) inferInstance)
      (field_isGorensteinRing k)
  have : Module.Invertible B (Module.Dual k B) := invertible_dual_of_isGorensteinRing hG
  exact Module.Invertible.congr
    ((dualizingModuleEquiv F (selfFactorization k B)).trans selfFactorizationDualEquiv).symm

end Stacks.Discriminant

end
