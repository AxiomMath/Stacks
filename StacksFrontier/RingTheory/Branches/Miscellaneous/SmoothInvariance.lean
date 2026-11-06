module


public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Unramified.LocalRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Branches.Defs
public import StacksFrontier.RingTheory.Branches.Henselization
public import StacksFrontier.RingTheory.Branches.UnibranchEtale
public import StacksFrontier.RingTheory.Etale.FilteredColimit.Basic
public import StacksFrontier.RingTheory.GeometricallyIntegral.TFAE
public import StacksFrontier.RingTheory.GeometricallyIntegral.TensorProduct
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.GeometricallyNormal.TensorProduct
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.Henselization.TensorProduct
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.Henselian.Quotient
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.TensorProduct
public import StacksFrontier.RingTheory.HenselizationUniverse.StrictTensorProduct
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Smooth.Normal
public import StacksFrontier.RingTheory.Smooth.Reduced
public import StacksFrontier.RingTheory.TensorProduct.LocalAlgebra
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
public import StacksFrontier.RingTheory.Unramified.LocalStructure
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksFrontier.RingTheory.WeaklyEtale.Flat
public import StacksFrontier.RingTheory.Branches.Miscellaneous.StrictHenselizationTensorProduct
import StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapAtGenericFibre
import StacksFrontier.RingTheory.AdicCompletion.FiniteBaseChange
import StacksFrontier.RingTheory.Branches.Completion
import StacksFrontier.RingTheory.Henselian.StrictHenselization.Quotient

@[expose] public section

/-!
# Branches: invariance of branch numbers under localizations of smooth maps

Branch numbers are invariant under a local homomorphism of local rings that is a localization of
a smooth ring map: the number of geometric branches is always preserved, and the ordinary number
of branches is preserved as soon as the induced extension of residue fields is purely
inseparable.

## Main results

* `numberOfBranches_eq_of_isLocalization_smooth` (Stacks 0DQ1): invariance of the number of
  geometric branches under a localization of a smooth local map, and invariance of the ordinary
  number of branches when the residue-field extension is purely inseparable.

## Implementation notes

Saying that a map is a localization of a smooth map is expressed by a smooth intermediate algebra
together with a localization algebra structure on the target compatible with the given map.

`IsLocalRing.IsHenselization R L Rh` leaves the universe of `Rh` independent of that of `R`, and
Tag 0DQ1 is stated here at the source's own strength: `A` with its henselization and strict
henselization in one universe, `B` with its two in another, and the two separable closures in two
more. What used to tie all six rings together were the two results the proof rests on, Stacks 08HU
and 08HV, whose providers in `StacksFrontier/RingTheory/Henselian/` take source, target, their
localizations and their henselizations in a single universe. They are used here through
`StacksDraft.henselization_tensorProduct_at_unique_prime` and
`StacksDraft.strictHenselization_tensorProduct_at_induced_prime`, the source-strength forms of the
same two statements, which is what lets the two families separate; the branch-counting lemmas of
the `SmoothInvariance` section are correspondingly stated with the base and its henselization in
independent universes.

Flatness of a henselization over its base is taken from
`StacksFrontier.RingTheory.Branches.Henselization` (`flat_of_isHenselization`).

## References

* [The Stacks Project, Tag 0DQ1](https://stacks.math.columbia.edu/tag/0DQ1)
-/

universe u v w uA uB uC uN vA vB

section SmoothInvariance

open scoped TensorProduct
open IsLocalRing
open CategoryTheory CategoryTheory.Limits

private theorem flat_of_isLocalization_smooth
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (hsm : ∃ (C : Type uC) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (S : Submonoid C),
        Algebra.Smooth A C ∧ IsLocalization S B) : Module.Flat A B := by
  obtain ⟨C, hC, hAC, hCB, hABC, S, hsmooth, hloc⟩ := hsm
  let : CommRing C := hC
  let : Algebra A C := hAC
  let : Algebra C B := hCB
  let : IsScalarTower A C B := hABC
  let : Algebra.Smooth A C := hsmooth
  let : IsLocalization S B := hloc
  have : Module.Flat C B := IsLocalization.flat B S
  exact Module.Flat.trans A C B


private theorem isDomain_of_isUnibranch_of_normal_tensorProduct
    {R : Type u} {B : Type v} [CommRing R] [IsLocalRing R] [IsDomain R]
    [CommRing B] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    [Module.Flat R B] (hu : IsUnibranch R)
    (hi : IsGeometricallyUnibranch R ∨
      (ResidueField.map (algebraMap R B)).IsPurelyInseparable)
    (hn : ∀ (C : Type u) [CommRing C] [Algebra R C],
      IsNormalRing C → IsNormalRing (B ⊗[R] C)) : IsDomain B := by
  let Rred := R ⧸ nilradical R
  let C := integralClosure Rred (FractionRing Rred)
  have hred : IsDomain Rred := hu.1
  have hC : IsLocalRing C := hu.2
  have : IsLocalRing Rred :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap R Rred) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hCint : IsIntegrallyClosed C :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing Rred)
  have hCnormal : IsNormalRing C := fun p _ =>
    ⟨IsLocalization.isDomain_of_local_atPrime ‹p.IsPrime›,
      isIntegrallyClosed_of_isLocalization (S := Localization.AtPrime p)
        p.primeCompl p.primeCompl_le_nonZeroDivisors⟩
  have hRredC : IsLocalHom (algebraMap Rred C) :=
    ((local_hom_TFAE (algebraMap Rred C)).out 5 1).mp <| (maximal_ideal_unique Rred).unique
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Rred) (maximalIdeal C)) inferInstance
  have hRC : IsLocalHom (algebraMap R C) := by
    rw [IsScalarTower.algebraMap_eq R Rred C]
    exact RingHom.isLocalHom_comp _ _
  have hintegral : Algebra.IsIntegral R C := Algebra.IsIntegral.trans Rred
  have hins :
      @IsPurelyInseparable (ResidueField R) (ResidueField C) _ _
        (ResidueField.map (algebraMap R C)).toAlgebra ∨
      @IsPurelyInseparable (ResidueField R) (ResidueField B) _ _
        (ResidueField.map (algebraMap R B)).toAlgebra :=
    hi.imp_left fun h => h.2 hred hC
  have hlocal : IsLocalRing (B ⊗[R] C) := (isLocalRing_tensorProduct_of_isIntegral R B C hins).1
  have hdom : IsDomain (B ⊗[R] C) := (IsNormalRing.of_isLocalRing (hn C hCnormal)).1
  have hinjred : Function.Injective (algebraMap R Rred) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    show RingHom.ker (Ideal.Quotient.mk (nilradical R)) = ⊥
    rw [Ideal.mk_ker, nilradical_eq_zero]
    rfl
  have hinjC : Function.Injective (algebraMap R C) := by
    rw [IsScalarTower.algebraMap_eq R Rred C]
    exact (FaithfulSMul.algebraMap_injective Rred C).comp hinjred
  exact Function.Injective.isDomain
    (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := C))
    (Algebra.TensorProduct.includeLeft_injective (R := R) (S := R) (A := B) (B := C) hinjC)

@[ega "0 23.2.1" "more general", ega "IV 18.6.13" "special case", ega "IV 18.8.16" "special case"]
private theorem isUnibranch_of_isDomain_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsDomain R] :
    IsUnibranch R := by
  have : IsHenselization R (ResidueField R) R := isHenselization_self R
  apply (isUnibranch_iff_henselization_has_unique_minimalPrime R R).mpr
  rw [IsDomain.minimalPrimes_eq_singleton_bot]
  exact ⟨⊥, rfl, fun _ h => h⟩

@[ega "0 23.2.1" "special case", ega "IV 18.8.16" "special case"]
private theorem isGeometricallyUnibranch_of_isDomain_of_strictHenselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R] [IsDomain R]
    [IsSepClosed (ResidueField R)] : IsGeometricallyUnibranch R := by
  have : IsHenselization R (ResidueField R) R := isHenselization_self R
  apply (isGeometricallyUnibranch_iff_strictHenselization_has_unique_minimalPrime
    R R (ResidueField R)).mpr
  rw [IsDomain.minimalPrimes_eq_singleton_bot]
  exact ⟨⊥, rfl, fun _ h => h⟩

private theorem injOn_minimalPrimes_comap_of_isPrime_map
    {R B : Type*} [CommRing R] [CommRing B] (f : R →+* B)
    (hp : ∀ q ∈ minimalPrimes B, (Ideal.map f (q.comap f)).IsPrime) :
    Set.InjOn (Ideal.comap f) (minimalPrimes B) := by
  intro q hq q' hq' heq
  have he (a : Ideal B) (ha : a ∈ minimalPrimes B) : a = (a.comap f).map f :=
    le_antisymm (ha.2 ⟨hp a ha, bot_le⟩ Ideal.map_comap_le) Ideal.map_comap_le
  rw [he q hq, he q' hq', heq]

private theorem isPurelyInseparable_of_commutative_square
    {K L K' L' : Type*} [Field K] [Field L] [Field K'] [Field L']
    (f : K →+* L) (g : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (h : g.comp eK.toRingHom = eL.toRingHom.comp f)
    (hf : f.IsPurelyInseparable) : g.IsPurelyInseparable := by
  have hg : g = eL.toRingHom.comp (f.comp eK.symm.toRingHom) := by
    ext x
    simpa using DFunLike.congr_fun h (eK.symm x)
  rw [hg]
  exact ((RingHom.isPurelyInseparable_of_surjective eK.symm.toRingHom
    eK.symm.surjective).comp hf).comp
    (RingHom.isPurelyInseparable_of_surjective eL.toRingHom eL.surjective)

set_option backward.isDefEq.respectTransparency false in
private theorem isPrime_map_of_normal_tensorProduct
    {R : Type u} {B : Type v} [CommRing R] [HenselianLocalRing R]
    [CommRing B] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    [Module.Flat R B] (p : Ideal R) [p.IsPrime]
    (hi : IsSepClosed (ResidueField R) ∨
      (ResidueField.map (algebraMap R B)).IsPurelyInseparable)
    (hn : ∀ (C : Type u) [CommRing C] [Algebra R C],
      IsNormalRing C → IsNormalRing (B ⊗[R] C)) :
    (p.map (algebraMap R B)).IsPrime := by
  let Q := R ⧸ p
  let I := p.map (algebraMap R B)
  let D := B ⧸ I
  have hI : I ≤ maximalIdeal B :=
    (Ideal.map_le_iff_le_comap).mpr (by
      rw [IsLocalRing.maximalIdeal_comap]
      exact IsLocalRing.le_maximalIdeal (inferInstance : p.IsPrime).ne_top)
  have hIne : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hI
  have : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalRing D :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : HenselianLocalRing Q :=
    Stacks.Henselian.henselianLocalRing_quotient (inferInstance : p.IsPrime).ne_top
  have : IsLocalHom (algebraMap R Q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap B D) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : IsLocalHom (algebraMap Q D) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : IsUnit (algebraMap R B r) :=
      isUnit_of_map_unit (algebraMap B D) _ hx
    exact (isUnit_of_map_unit (algebraMap R B) _ hr).map (algebraMap R Q)
  have : Module.Flat Q D :=
    Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B p).toLinearEquiv
  let eR : ResidueField R ≃+* ResidueField Q := RingEquiv.ofBijective _
    (Stacks.StrictHenselization.QuotientDescent.residueField_map_bijective_of_surjective
      (algebraMap R Q) Ideal.Quotient.mk_surjective)
  let eB : ResidueField B ≃+* ResidueField D := RingEquiv.ofBijective _
    (Stacks.StrictHenselization.QuotientDescent.residueField_map_bijective_of_surjective
      (algebraMap B D) Ideal.Quotient.mk_surjective)
  have hiQ : IsGeometricallyUnibranch Q ∨
      (ResidueField.map (algebraMap Q D)).IsPurelyInseparable := by
    rcases hi with h | h
    · have : IsSepClosed (ResidueField R) := h
      have : IsSepClosed (ResidueField Q) :=
        Stacks.StrictHenselization.EtaleColimit.isSepClosed_of_ringEquiv eR
      exact Or.inl (isGeometricallyUnibranch_of_isDomain_of_strictHenselianLocalRing Q)
    · refine Or.inr (isPurelyInseparable_of_commutative_square
        (ResidueField.map (algebraMap R B)) (ResidueField.map (algebraMap Q D)) eR eB ?_ h)
      show (ResidueField.map (algebraMap Q D)).comp (ResidueField.map (algebraMap R Q)) =
        (ResidueField.map (algebraMap B D)).comp (ResidueField.map (algebraMap R B))
      ext x
      obtain ⟨r, rfl⟩ := residue_surjective x
      simp only [RingHom.comp_apply, ResidueField.map_residue]
      rfl
  have hDn : ∀ (C : Type u) [CommRing C] [Algebra Q C],
      IsNormalRing C → IsNormalRing (D ⊗[Q] C) := by
    intro C _ _ hC
    let : Algebra R C := ((algebraMap Q C).comp (algebraMap R Q)).toAlgebra
    have : IsScalarTower R Q C := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let e := (Algebra.TensorProduct.comm Q D C).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : C ≃ₐ[C] C)
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B p)).trans
        (Algebra.TensorProduct.cancelBaseChange R Q C C B)).toRingEquiv
    exact IsNormalRing.congr e.symm
      (IsNormalRing.congr (Algebra.TensorProduct.comm R B C).toRingEquiv (hn C hC))
  have : IsDomain D := isDomain_of_isUnibranch_of_normal_tensorProduct
    (isUnibranch_of_isDomain_of_henselianLocalRing Q) hiQ hDn
  exact (Ideal.Quotient.isDomain_iff_prime (I := I)).mp inferInstance

private theorem encard_minimalPrimes_eq_of_normal_tensorProduct
    {R : Type u} {B : Type v} [CommRing R] [HenselianLocalRing R]
    [CommRing B] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    [Module.Flat R B]
    (hi : IsSepClosed (ResidueField R) ∨
      (ResidueField.map (algebraMap R B)).IsPurelyInseparable)
    (hn : ∀ (C : Type u) [CommRing C] [Algebra R C],
      IsNormalRing C → IsNormalRing (B ⊗[R] C)) :
    (minimalPrimes R).encard = (minimalPrimes B).encard := by
  have : Module.FaithfullyFlat R B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  apply encard_minimalPrimes_eq_of_injOn_comap
  apply injOn_minimalPrimes_comap_of_isPrime_map
  intro q hq
  have : (q.comap (algebraMap R B)).IsPrime := hq.isPrime.comap _
  exact isPrime_map_of_normal_tensorProduct _ hi hn

set_option backward.isDefEq.respectTransparency false in
private theorem isNormalRing_tensorProduct_of_henselization_baseChange
    {A R : Type u} {B H : Type v} {L : Type*}
    [CommRing A] [CommRing R] [CommRing B] [CommRing H]
    [Algebra A R] [Algebra A B] [Algebra A H] [Algebra R H] [Algebra B H]
    [IsScalarTower A R H] [IsScalarTower A B H]
    (Q : Ideal (R ⊗[A] B)) [Q.IsPrime]
    [Algebra (Localization.AtPrime Q) H]
    [Field L] [Algebra (ResidueField (Localization.AtPrime Q)) L]
    [IsLocalRing H] [IsHenselization (Localization.AtPrime Q) L H]
    (hcomp : (algebraMap (Localization.AtPrime Q) H).comp
      (algebraMap (R ⊗[A] B) (Localization.AtPrime Q)) =
        (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A R H)
          (IsScalarTower.toAlgHom A B H) (fun _ _ => Commute.all _ _)).toRingHom)
    (hn : ∀ (N : Type u) [CommRing N] [Algebra A N],
      IsNormalRing N → IsNormalRing (N ⊗[A] B))
    (N : Type u) [CommRing N] [Algebra R N] (hN : IsNormalRing N) :
    IsNormalRing (H ⊗[R] N) := by
  let U := R ⊗[A] B
  let T := Localization.AtPrime Q
  let : Algebra A N := ((algebraMap R N).comp (algebraMap A R)).toAlgebra
  have : IsScalarTower A R N := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R T H := IsScalarTower.of_algebraMap_eq fun r => by
    have h := DFunLike.congr_fun hcomp (r ⊗ₜ[A] (1 : B))
    change algebraMap T H (algebraMap U T (r ⊗ₜ[A] (1 : B))) =
      Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A R H)
        (IsScalarTower.toAlgHom A B H) _ (r ⊗ₜ[A] (1 : B)) at h
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one] at h
    exact h.symm
  have hNU : IsNormalRing (N ⊗[R] U) :=
    IsNormalRing.congr (Algebra.TensorProduct.cancelBaseChange A R N N B).symm.toRingEquiv
      (hn N hN)
  let F : (N ⊗[R] U) →ₐ[R] (N ⊗[R] T) :=
    Algebra.TensorProduct.map (AlgHom.id R N) (IsScalarTower.toAlgHom R U T)
  let : Algebra (N ⊗[R] U) (N ⊗[R] T) := F.toRingHom.toAlgebra
  have : IsScalarTower N (N ⊗[R] U) (N ⊗[R] T) := by
    apply IsScalarTower.of_algebraMap_eq (R := N) (S := N ⊗[R] U) (A := N ⊗[R] T)
    intro n
    show n ⊗ₜ[R] (1 : T) = F (n ⊗ₜ[R] (1 : U))
    simp only [F, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  have : IsLocalization
      (Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := R) (A := N)))
      (N ⊗[R] T) :=
    IsLocalization.tensorProduct_tensorProduct_right R N Q.primeCompl T
      (by
        apply RingHom.ext
        intro u
        show F ((1 : N) ⊗ₜ[R] u) = (1 : N) ⊗ₜ[R] algebraMap U T u
        dsimp only [F]
        rw [Algebra.TensorProduct.map_tmul]
        rfl)
  have hNT : IsNormalRing (N ⊗[R] T) := hNU.isLocalization
    (Q.primeCompl.map (Algebra.TensorProduct.includeRight (R := R) (A := N))) _
  have hTN : IsNormalRing (T ⊗[R] N) :=
    IsNormalRing.congr (Algebra.TensorProduct.comm R N T).toRingEquiv hNT
  have hTH : IsNormalRing (H ⊗[T] (T ⊗[R] N)) :=
    isNormalRing_baseChange_henselization T H (T ⊗[R] N) L hTN
  exact IsNormalRing.congr
    (Algebra.TensorProduct.cancelBaseChange R T H H N).toRingEquiv hTH

private theorem encard_minimalPrimes_eq_of_henselization_baseChange
    {A R : Type u} {B H : Type v} {K L M : Type*}
    [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [CommRing B] [IsLocalRing B] [CommRing H] [IsLocalRing H]
    [Algebra A R] [Algebra A B] [Algebra A H] [Algebra R H] [Algebra B H]
    [IsScalarTower A R H] [IsScalarTower A B H] [IsLocalHom (algebraMap R H)]
    [Field K] [Algebra (ResidueField A) K] [IsHenselization A K R]
    [Field L] [Algebra (ResidueField B) L] [IsHenselization B L H]
    (hsm : ∃ (C : Type uC) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (S : Submonoid C),
        Algebra.Smooth A C ∧ IsLocalization S B)
    (Q : Ideal (R ⊗[A] B)) [Q.IsPrime] [Algebra (Localization.AtPrime Q) H]
    [Field M] [Algebra (ResidueField (Localization.AtPrime Q)) M]
    [IsHenselization (Localization.AtPrime Q) M H]
    (hcomp : (algebraMap (Localization.AtPrime Q) H).comp
      (algebraMap (R ⊗[A] B) (Localization.AtPrime Q)) =
        (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A R H)
          (IsScalarTower.toAlgHom A B H) (fun _ _ => Commute.all _ _)).toRingHom)
    (hi : IsSepClosed (ResidueField R) ∨
      (ResidueField.map (algebraMap R H)).IsPurelyInseparable) :
    (minimalPrimes R).encard = (minimalPrimes H).encard := by
  have : Module.Flat A B := flat_of_isLocalization_smooth hsm
  have : Module.Flat B H := flat_of_isHenselization (L := L)
  have : Module.Flat A H := Module.Flat.trans A B H
  have : Module.Flat R H := flat_restrictScalars_of_ind_etale A R H
    (IsHenselization.ind_etale_of_universe_le.{u, _, u} (R := A) (L := K) (Rh := R))
  have : HenselianLocalRing R := IsHenselization.henselian A K
  apply encard_minimalPrimes_eq_of_normal_tensorProduct hi
  intro N _ _ hN
  apply isNormalRing_tensorProduct_of_henselization_baseChange (L := M) Q hcomp _ N hN
  intro N _ _ hN
  obtain ⟨C, hC, hAC, hCB, hTower, S, hSmooth, hLoc⟩ := hsm
  let := hC
  let := hAC
  let := hCB
  let := hTower
  let := hSmooth
  let := hLoc
  exact Algebra.isNormalRing_tensorProduct_of_smooth_of_isLocalization A N C B hN S


/-- A local homomorphism of local rings which is a localization of a smooth ring map preserves
the number of geometric branches. If its residue-field extension is purely inseparable, it also
preserves the number of branches.

The source's two rings carry independent universes, together with their henselizations and
strict henselizations: `A`, `Aʰ`, `Aˢʰ` in one and `B`, `Bʰ`, `Bˢʰ` in the other, and the two
separable closures in two more. The universe work is done by
`StacksDraft.henselization_tensorProduct_at_unique_prime` and
`StacksDraft.strictHenselization_tensorProduct_at_induced_prime`, the source-strength forms of
tags 08HU and 08HV, and by the ind-étale layer they are built on, which lets the branch-counting
lemmas above be stated with the base and its henselization in independent universes. -/
@[stacks 0DQ1]
theorem numberOfBranches_eq_of_isLocalization_smooth
    (A Ah Ash : Type uA) (B Bh Bsh : Type uB) (kAsep : Type vA) (kBsep : Type vB)
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    (hsm : ∃ (C : Type uC) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (S : Submonoid C),
        Algebra.Smooth A C ∧ IsLocalization S B)
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Ah]
    [CommRing Bh] [IsLocalRing Bh] [Algebra B Bh]
    [IsLocalRing.IsHenselization B (IsLocalRing.ResidueField B) Bh]
    [Field kAsep] [Algebra (IsLocalRing.ResidueField A) kAsep]
    [IsSepClosure (IsLocalRing.ResidueField A) kAsep]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [IsLocalRing.IsHenselization A kAsep Ash]
    [Field kBsep] [Algebra (IsLocalRing.ResidueField B) kBsep]
    [IsSepClosure (IsLocalRing.ResidueField B) kBsep]
    [CommRing Bsh] [IsLocalRing Bsh] [Algebra B Bsh]
    [IsLocalRing.IsHenselization B kBsep Bsh] :
    numberOfGeometricBranches A kAsep Ash = numberOfGeometricBranches B kBsep Bsh ∧
      ((IsLocalRing.ResidueField.map (algebraMap A B)).IsPurelyInseparable →
        numberOfBranches A Ah = numberOfBranches B Bh) := by
  classical
  let : Algebra A Bh := ((algebraMap B Bh).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B Bh := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra A Bsh := ((algebraMap B Bsh).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B Bsh := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalHom (algebraMap A Ah) := IsHenselization.isLocalHom (L := ResidueField A)
  have : IsLocalHom (algebraMap A Ash) := IsHenselization.isLocalHom (L := kAsep)
  have : IsLocalHom (algebraMap B Bh) := IsHenselization.isLocalHom (L := ResidueField B)
  have : IsLocalHom (algebraMap B Bsh) := IsHenselization.isLocalHom (L := kBsep)
  have : IsLocalHom (algebraMap A Bh) := RingHom.isLocalHom_comp _ _
  have : IsLocalHom (algebraMap A Bsh) := RingHom.isLocalHom_comp _ _
  have : IsLocalization.AtPrime A (maximalIdeal A) :=
    IsLocalRing.isLocalization_atPrime_maximalIdeal A
  have : IsLocalization.AtPrime B (maximalIdeal B) :=
    IsLocalRing.isLocalization_atPrime_maximalIdeal B
  have : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨(maximalIdeal_comap (algebraMap A B)).symm⟩
  constructor
  · obtain ⟨algResA, hHA, hsepA, hresA⟩ :=
      IsHenselization.exists_residueFieldAlgebra (R := A) (L := kAsep) (Rh := Ash)
    let := algResA
    have : IsHenselization A (ResidueField Ash) Ash := hHA
    have : IsSepClosure (ResidueField A) (ResidueField Ash) := hsepA inferInstance
    have : IsSepClosed (ResidueField Ash) := IsSepClosure.sep_closed (ResidueField A)
    obtain ⟨algResB, hHB, hsepB, hresB⟩ :=
      IsHenselization.exists_residueFieldAlgebra (R := B) (L := kBsep) (Rh := Bsh)
    let := algResB
    have : IsHenselization B (ResidueField Bsh) Bsh := hHB
    have : IsSepClosure (ResidueField B) (ResidueField Bsh) := hsepB inferInstance
    have : IsSepClosed (ResidueField Bsh) := IsSepClosure.sep_closed (ResidueField B)
    let : Algebra (ResidueField A) (ResidueField Bsh) :=
      (ResidueField.map (algebraMap A Bsh)).toAlgebra
    let phi : ResidueField Ash →ₐ[ResidueField A] ResidueField Bsh := IsSepClosed.lift
    have hphi : phi.toRingHom.comp ((residue Ash).comp (algebraMap A Ash)) =
        (residue Bsh).comp (algebraMap A Bsh) := by
      ext x
      show phi (residue Ash (algebraMap A Ash x)) = residue Bsh (algebraMap A Bsh x)
      rw [← hresA x, phi.commutes]
      exact ResidueField.map_residue (algebraMap A Bsh) x
    obtain ⟨f, hf, _, _, Q, hQ, _, _, _, algTH, hTHlocal, algResT,
        hsepT, hHT, _, hcomp⟩ :=
      StacksDraft.strictHenselization_tensorProduct_at_induced_prime
        (R := A) (Rp := A) (Rsh := Ash) (S := B) (Sq := B) (Ssh := Bsh)
        (maximalIdeal A) (maximalIdeal B) phi.toRingHom hphi
    let : Algebra Ash Bsh := f.toRingHom.toAlgebra
    have : IsScalarTower A Ash Bsh := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
    have : IsLocalHom (algebraMap Ash Bsh) := ⟨fun x hx => hf.map_nonunit x hx⟩
    let : Q.IsPrime := hQ
    let := algTH
    let := hTHlocal
    let := algResT
    let := hHT
    show (minimalPrimes Ash).encard = (minimalPrimes Bsh).encard
    exact encard_minimalPrimes_eq_of_henselization_baseChange
      (K := kAsep) (L := kBsep) (M := ResidueField Bsh) hsm Q hcomp (Or.inl inferInstance)
  · intro hpi
    obtain ⟨f, hf, _, _, Q, hQ, _, _, _, _, algTH, hTHlocal, hHT, hcomp⟩ :=
      StacksDraft.henselization_tensorProduct_at_unique_prime
        (R := A) (Rp := A) (Rh := Ah) (S := B) (Sq := B) (Sh := Bh)
        (maximalIdeal A) (maximalIdeal B)
    let : Algebra Ah Bh := f.toRingHom.toAlgebra
    have : IsScalarTower A Ah Bh := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
    have : IsLocalHom (algebraMap Ah Bh) := ⟨fun x hx => hf.map_nonunit x hx⟩
    let : Q.IsPrime := hQ
    let := algTH
    let := hTHlocal
    let := hHT
    let eA : ResidueField A ≃+* ResidueField Ah := RingEquiv.ofBijective _
      (IsHenselization.residueField_map_bijective (R := A) (Rh := Ah))
    let eB : ResidueField B ≃+* ResidueField Bh := RingEquiv.ofBijective _
      (IsHenselization.residueField_map_bijective (R := B) (Rh := Bh))
    have hpi' : (ResidueField.map (algebraMap Ah Bh)).IsPurelyInseparable := by
      apply isPurelyInseparable_of_commutative_square (ResidueField.map (algebraMap A B))
        (ResidueField.map (algebraMap Ah Bh)) eA eB _ hpi
      ext x
      obtain ⟨r, rfl⟩ := residue_surjective x
      show ResidueField.map (algebraMap Ah Bh)
          (ResidueField.map (algebraMap A Ah) (residue A r)) =
        ResidueField.map (algebraMap B Bh) (ResidueField.map (algebraMap A B) (residue A r))
      simp only [ResidueField.map_residue]
      rw [← IsScalarTower.algebraMap_apply A Ah Bh, ← IsScalarTower.algebraMap_apply A B Bh]
    show (minimalPrimes Ah).encard = (minimalPrimes Bh).encard
    exact encard_minimalPrimes_eq_of_henselization_baseChange
      (K := ResidueField A) (L := ResidueField B)
      (M := ResidueField (Localization.AtPrime Q)) hsm Q hcomp (Or.inr hpi')

end SmoothInvariance

end
