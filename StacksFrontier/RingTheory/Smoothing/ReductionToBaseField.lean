module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Localization.FractionRing
public import StacksFrontier.RingTheory.MinimalPrimes.Reduced
public import StacksFrontier.RingTheory.Noetherian.Spec
public import StacksFrontier.RingTheory.Regular.RegularRingHom
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.Smoothing.CommonDesingularization
public import StacksFrontier.RingTheory.Smoothing.DelocalizingSmoothFactorization
public import StacksFrontier.RingTheory.Smoothing.IndSmooth
public import StacksFrontier.RingTheory.Smoothing.LiftingLemma
public import StacksFrontier.RingTheory.Smoothing.LiftingProblem
public import StacksFrontier.RingTheory.Smoothing.RegularRingMap
public import StacksFrontier.RingTheory.Smoothing.SingularIdeals
public import StacksFrontier.RingTheory.Smoothing.StandardnessConditions

/-!
# Reduction of Popescu approximation to a base field

Property PT of Situation 16.8.1 — for a regular ring map `R → Λ` of Noetherian rings, that `Λ` is
a filtered colimit of smooth `R`-algebras — holds in general as soon as it holds whenever the base
ring is a field.

## Main results

* `Stacks.Smoothing.indSmooth_of_indSmooth_of_field_base`: property PT reduces to a base field.

## Implementation notes

Situation 16.8.1 is `Stacks.Smoothing.IsRegularRingMap` together with the Noetherian
hypotheses, and "PT holds for `R → Λ`" is `Stacks.Smoothing.IndSmooth`, the `ObjectProperty.ind`
spelling of "`Λ` is a filtered colimit of smooth `R`-algebras" used in Lemma `07C3`.

The proof is the source's. Noetherian induction on the ideals `I` for which `R/I → Λ/IΛ` fails PT
produces a maximal failure, which by Proposition `07CM`
(`Stacks.Smoothing.ind_smooth_of_isNilpotent`) forces `R` to be reduced; the total ring
of fractions of a reduced Noetherian ring is a finite product of fields (Lemmas `02LX`, `00FR`),
so PT over fields and Lemma `07F3` give PT after inverting the nonzerodivisors; Lemma `07F4`
delocalizes the resulting smooth factorization to one in which a nonzerodivisor `π` is elementary,
hence strictly, standard (Lemma `07EZ`); and PT modulo `π⁸` together with Lemmas `07CP` and `07CT`
assembles the required smooth factorization over `R` itself.

## References

* [Stacks Project, Tag 07F5](https://stacks.math.columbia.edu/tag/07F5)
-/

open scoped TensorProduct

@[expose] public section

namespace Stacks.Smoothing

open CategoryTheory CategoryTheory.Limits

universe u

section Regularity

private theorem regularRingHom_of_isRegularRingMap
    (R : Type u) (Λ : Type u) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing Λ] (h : IsRegularRingMap R Λ) :
    IsRegularRingHom (algebraMap R Λ) := by
  rw [isRegularRingHom_algebraMap_iff]
  refine ⟨RingHom.flat_algebraMap_iff.mpr h.1, ?_⟩
  intro p hp
  let : p.IsPrime := hp
  let : Algebra Λ (p.Fiber Λ) := Algebra.TensorProduct.rightAlgebra
  let : Algebra p.ResidueField (p.Fiber Λ) := Algebra.TensorProduct.leftAlgebra
  refine ⟨p.isNoetherianRing_fiber Λ, ?_⟩
  refine ⟨(Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    p.ResidueField (p.Fiber Λ)).2 ?_⟩
  intro K _ _ _ hpi
  let : Algebra R K :=
    ((algebraMap p.ResidueField K).comp (algebraMap R p.ResidueField)).toAlgebra
  let : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e := Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K Λ
  exact @IsRegularRing.of_ringEquiv _ _ _ _ e.symm.toRingEquiv (h.2 p K).2

public theorem isRegularRingMap_of_regularRingHom
    (R : Type u) (Λ : Type u) [CommRing R] [CommRing Λ] [Algebra R Λ]
    (h : IsRegularRingHom (algebraMap R Λ)) : IsRegularRingMap R Λ := by
  rw [isRegularRingHom_algebraMap_iff] at h
  refine ⟨RingHom.flat_algebraMap_iff.mp h.1, ?_⟩
  intro p hp K _ _ _
  let : Algebra R K :=
    ((algebraMap p.ResidueField K).comp (algebraMap R p.ResidueField)).toAlgebra
  let : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra Λ (p.Fiber Λ) := Algebra.TensorProduct.rightAlgebra
  let : Algebra p.ResidueField (p.Fiber Λ) := Algebra.TensorProduct.leftAlgebra
  let : Algebra p.ResidueField K := inferInstance
  let : Algebra K (K ⊗[p.ResidueField] (p.Fiber Λ)) := Algebra.TensorProduct.leftAlgebra
  let : Algebra (p.Fiber Λ) (K ⊗[p.ResidueField] (p.Fiber Λ)) :=
    Algebra.TensorProduct.rightAlgebra
  let e := Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K Λ
  have hNoeth : IsNoetherianRing (K ⊗[R] Λ) := by
    have : IsNoetherianRing (p.Fiber Λ) := (h.2 p).1
    have : IsNoetherianRing (p.Fiber Λ ⊗[p.ResidueField] K) :=
      Algebra.FiniteType.isNoetherianRing (p.Fiber Λ) (p.Fiber Λ ⊗[p.ResidueField] K)
    have : IsNoetherianRing (K ⊗[p.ResidueField] (p.Fiber Λ)) :=
      isNoetherianRing_of_ringEquiv _
        (Algebra.TensorProduct.comm p.ResidueField (p.Fiber Λ) K).toRingEquiv
    exact isNoetherianRing_of_ringEquiv _ e.toRingEquiv
  have : IsRegularRing (K ⊗[p.ResidueField] (p.Fiber Λ)) :=
    (h.2 p).2.isRegularRing_tensorProduct K
  exact ⟨hNoeth, IsRegularRing.of_ringEquiv e.toRingEquiv⟩

private theorem regularRingHom_of_algEquiv
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] (B : Type u) [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B)
    (h : IsRegularRingHom (algebraMap R A)) : IsRegularRingHom (algebraMap R B) := by
  rw [isRegularRingHom_algebraMap_iff] at h ⊢
  have hflat : (algebraMap R B).Flat := by
    have hmap : algebraMap R B = e.toRingEquiv.toRingHom.comp (algebraMap R A) := by
      ext r
      exact (e.commutes r).symm
    rw [hmap]
    exact RingHom.Flat.comp h.1 (RingHom.Flat.of_bijective e.bijective)
  refine ⟨hflat, ?_⟩
  intro p hp
  let : IsNoetherianRing (p.Fiber A) := (h.2 p).1
  let eF : p.Fiber A ≃ₐ[p.ResidueField] p.Fiber B :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : p.ResidueField ≃ₐ[p.ResidueField]
      p.ResidueField) e
  refine ⟨isNoetherianRing_of_ringEquiv _ eF.toRingEquiv, ?_⟩
  refine ⟨fun K _ _ _ => ?_⟩
  let : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber A) := (h.2 p).2
  let : CommRing (K ⊗[p.ResidueField] (p.Fiber A)) := Algebra.TensorProduct.instCommRing
  let : CommRing (K ⊗[p.ResidueField] (p.Fiber B)) := Algebra.TensorProduct.instCommRing
  have : IsRegularRing (K ⊗[p.ResidueField] (p.Fiber A)) :=
    Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct K
  let eK := Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[p.ResidueField] K) eF
  exact IsRegularRing.of_ringEquiv eK.toRingEquiv

private theorem isGeometricallyRegular_of_algEquiv
    {k : Type u} {A : Type u} {B : Type u}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra.IsGeometricallyRegular k A] (e : A ≃ₐ[k] B) :
    Algebra.IsGeometricallyRegular k B := by
  refine ⟨fun K _ _ _ => ?_⟩
  have hreg := Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct (k := k) (R := A) K
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[k] K) e).toRingEquiv

private theorem regularRingHom_baseChange_essFiniteType
    (R : Type u) (Λ : Type u) (R' : Type u)
    [CommRing R] [CommRing Λ] [CommRing R'] [Algebra R Λ] [Algebra R R']
    [Algebra.EssFiniteType R R'] (h : IsRegularRingHom (algebraMap R Λ)) :
    IsRegularRingHom
      (Algebra.TensorProduct.includeRight (R := R) (A := Λ) (B := R')).toRingHom := by
  let : Algebra R' (Λ ⊗[R] R') := Algebra.TensorProduct.rightAlgebra
  rw [isRegularRingHom_algebraMap_iff] at h
  rw [isRegularRingHom_iff_of_eq_algebraMap _ (by rfl)]
  constructor
  · let : Module.Flat R Λ := RingHom.flat_algebraMap_iff.mp h.1
    show Module.Flat R' (Λ ⊗[R] R')
    exact Module.Flat.of_linearEquiv
      (Algebra.TensorProduct.commRight R R' Λ).symm.toLinearEquiv
  · intro p' hp'
    let : p'.IsPrime := hp'
    let p : Ideal R := p'.comap (algebraMap R R')
    let : p.IsPrime := Ideal.IsPrime.comap (algebraMap R R')
    let : p'.LiesOver p := ⟨rfl⟩
    let := Localization.AtPrime.algebraOfLiesOver p p'
    let : Algebra p.ResidueField (p.Fiber Λ) := Algebra.TensorProduct.leftAlgebra
    let e₁ := Algebra.TensorProduct.congr
      (AlgEquiv.refl : p'.ResidueField ≃ₐ[R'] p'.ResidueField)
      (Algebra.TensorProduct.commRight R R' Λ).symm
    let e₂ := (Algebra.TensorProduct.cancelBaseChange R R' p'.ResidueField
      p'.ResidueField Λ).trans
      (Algebra.TensorProduct.cancelBaseChange R p.ResidueField p'.ResidueField
        p'.ResidueField Λ).symm
    let e : p'.Fiber (Λ ⊗[R] R') ≃ₐ[p'.ResidueField]
        p'.ResidueField ⊗[p.ResidueField] (p.Fiber Λ) :=
      AlgEquiv.ofRingEquiv (f := e₁.toRingEquiv.trans e₂.toRingEquiv) (fun x => by
        show e₂ (e₁ (algebraMap p'.ResidueField _ x)) = algebraMap p'.ResidueField _ x
        rw [show e₁ (algebraMap p'.ResidueField _ x) = algebraMap p'.ResidueField _ x by
          simp [e₁, Algebra.TensorProduct.algebraMap_apply]]
        exact e₂.commutes x)
    have hp := h.2 p
    let : Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber Λ) := hp.2
    let : Algebra.EssFiniteType p.ResidueField p'.ResidueField := by
      have hess : Algebra.EssFiniteType R p'.ResidueField := .comp R R' _
      exact .of_comp R _ _
    let : CommRing (p'.ResidueField ⊗[p.ResidueField] (p.Fiber Λ)) :=
      Algebra.TensorProduct.instCommRing
    have hg : Algebra.IsGeometricallyRegular p'.ResidueField
        (p'.ResidueField ⊗[p.ResidueField] (p.Fiber Λ)) :=
      Stacks.GeometricallyRegular.SeparableBase.isGeometricallyRegular_tensorProduct
        p.ResidueField p'.ResidueField (p.Fiber Λ)
    have hg' : Algebra.IsGeometricallyRegular p'.ResidueField (p'.Fiber (Λ ⊗[R] R')) :=
      Algebra.IsGeometricallyRegular.of_algEquiv e.symm
    refine ⟨?_, hg'⟩
    have hreg := Algebra.IsGeometricallyRegular.isRegularRing_tensorProduct
      (k := p'.ResidueField) (R := p'.Fiber (Λ ⊗[R] R')) p'.ResidueField
    let : IsNoetherianRing
        (p'.ResidueField ⊗[p'.ResidueField] p'.Fiber (Λ ⊗[R] R')) := hreg.toIsNoetherian
    exact isNoetherianRing_of_ringEquiv _
      (Algebra.TensorProduct.lid p'.ResidueField (p'.Fiber (Λ ⊗[R] R'))).toRingEquiv

private theorem regularRingMap_residueFiber
    (R : Type u) (Λ : Type u) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing Λ] (p : Ideal R) [p.IsPrime] (h : IsRegularRingMap R Λ) :
    IsRegularRingMap p.ResidueField (p.Fiber Λ) := by
  let : Algebra p.ResidueField (Λ ⊗[R] p.ResidueField) := Algebra.TensorProduct.rightAlgebra
  have hbase := regularRingHom_baseChange_essFiniteType R Λ p.ResidueField
    (regularRingHom_of_isRegularRingMap R Λ h)
  let e₀ := Algebra.TensorProduct.comm R Λ p.ResidueField
  let e : (Λ ⊗[R] p.ResidueField) ≃ₐ[p.ResidueField] (p.ResidueField ⊗[R] Λ) :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (by
      intro x
      show e₀ (1 ⊗ₜ[R] x) = x ⊗ₜ[R] 1
      exact Algebra.TensorProduct.comm_tmul R (1 : Λ) x)
  let : Algebra Λ (p.Fiber Λ) := Algebra.TensorProduct.rightAlgebra
  let : Algebra p.ResidueField (p.Fiber Λ) := Algebra.TensorProduct.leftAlgebra
  have := p.isNoetherianRing_fiber Λ
  have hbase' : IsRegularRingHom (algebraMap p.ResidueField (Λ ⊗[R] p.ResidueField)) := hbase
  exact isRegularRingMap_of_regularRingHom p.ResidueField (p.Fiber Λ)
    (regularRingHom_of_algEquiv p.ResidueField (Λ ⊗[R] p.ResidueField)
      (p.ResidueField ⊗[R] Λ) e hbase')

/-- **Stacks 07C1 for Situation 16.8.1.** A regular ring map of Noetherian rings stays regular
after quotienting the base by an ideal. -/
private theorem regularRingMap_quotient
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Λ : Type u) [CommRing Λ] [Algebra R Λ] [IsNoetherianRing Λ]
    (I : Ideal R) (h : IsRegularRingMap R Λ) :
    IsRegularRingMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) := by
  let : Algebra (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : Algebra (R ⧸ I) (Λ ⊗[R] (R ⧸ I)) := Algebra.TensorProduct.rightAlgebra
  have hbase := isRegularRingHom_baseChange (R := R) (Λ := Λ) (R' := R ⧸ I)
    (regularRingHom_of_isRegularRingMap R Λ h)
  let eQ := Algebra.TensorProduct.quotIdealMapEquivQuotTensor Λ I
  let eComm := Algebra.TensorProduct.commRight R (R ⧸ I) Λ
  let e : (Λ ⧸ I.map (algebraMap R Λ)) ≃ₐ[R ⧸ I] (Λ ⊗[R] (R ⧸ I)) := eQ.trans eComm
  have hbase' : IsRegularRingHom (algebraMap (R ⧸ I) (Λ ⊗[R] (R ⧸ I))) := hbase
  exact isRegularRingMap_of_regularRingHom (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))
    (regularRingHom_of_algEquiv (R ⧸ I) (Λ ⊗[R] (R ⧸ I))
      (Λ ⧸ I.map (algebraMap R Λ)) e.symm hbase')

end Regularity

section MaximalFailure

private theorem exists_maximal_ideal_property
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (P : Ideal R → Prop) (hP : ∃ I, P I) : ∃ I, P I ∧ ∀ J, P J → ¬ I < J := by
  obtain ⟨I, hI, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {I | P I} hP
  exact ⟨I, hI, hmax⟩

/-- A maximal failure of PT forces the base to be reduced: Proposition `07CM` lifts PT across the
nilradical, which is nilpotent since `R` is Noetherian. -/
private theorem isReduced_of_indSmooth_on_nonzero_quotients
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Λ : Type u) [CommRing Λ] [Algebra R Λ]
    (hflat : Module.Flat R Λ) (hfail : ¬ IndSmooth R Λ)
    (hquot : ∀ I : Ideal R, I ≠ ⊥ → IndSmooth (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) :
    IsReduced R := by
  by_contra hred
  have hIne : nilradical R ≠ ⊥ := fun hzero => hred (nilradical_eq_bot_iff.mp hzero)
  let : Module.Flat R Λ := hflat
  exact hfail (ind_smooth_of_isNilpotent (R := R) (Λ := Λ) (nilradical R)
    (IsNoetherianRing.isNilpotent_nilradical R) (hquot (nilradical R) hIne))

private theorem indSmooth_quotient_of_maximal_bad
    (R : Type u) [CommRing R] (Λ : Type u) [CommRing Λ] [Algebra R Λ] (I : Ideal R)
    (hmax : ∀ K : Ideal R, I < K → IndSmooth (R ⧸ K) (Λ ⧸ K.map (algebraMap R Λ)))
    (J : Ideal (R ⧸ I)) (hJ : J ≠ ⊥) :
    IndSmooth ((R ⧸ I) ⧸ J)
      ((Λ ⧸ I.map (algebraMap R Λ)) ⧸
        J.map (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)))) := by
  let qR : R →+* R ⧸ I := Ideal.Quotient.mk I
  let K : Ideal R := J.comap qR
  have hIK : I ≤ K := by
    intro r hr
    show qR r ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact J.zero_mem
  have hJI : K.map qR = J := Ideal.map_comap_of_surjective qR Ideal.Quotient.mk_surjective J
  have hIKne : I ≠ K := by
    intro heq
    apply hJ
    rw [← hJI, ← heq]
    simp [qR]
  have hPTK := hmax K (lt_of_le_of_ne hIK hIKne)
  let M : Ideal Λ := I.map (algebraMap R Λ)
  let N : Ideal Λ := K.map (algebraMap R Λ)
  have hMN : M ≤ N := Ideal.map_mono hIK
  let qΛ : Λ →+* Λ ⧸ M := Ideal.Quotient.mk M
  let eR₀ : ((R ⧸ I) ⧸ J) ≃+* ((R ⧸ I) ⧸ K.map qR) := Ideal.quotientEquivAlgOfEq (R ⧸ I) hJI.symm
  let eR : ((R ⧸ I) ⧸ J) ≃+* (R ⧸ K) := eR₀.trans (DoubleQuot.quotQuotEquivQuotOfLE hIK)
  let eΛ : ((Λ ⧸ M) ⧸ N.map qΛ) ≃+* (Λ ⧸ N) := DoubleQuot.quotQuotEquivQuotOfLE hMN
  let : Algebra (R ⧸ I) (Λ ⧸ M) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : Algebra ((R ⧸ I) ⧸ J) ((Λ ⧸ M) ⧸ J.map (algebraMap (R ⧸ I) (Λ ⧸ M))) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let f : R ⧸ I →+* Λ ⧸ M := algebraMap (R ⧸ I) (Λ ⧸ M)
  have hf : f.comp qR = qΛ.comp (algebraMap R Λ) := by
    show (Ideal.quotientMap M (algebraMap R Λ) Ideal.le_comap_map).comp qR =
      qΛ.comp (algebraMap R Λ)
    exact Ideal.quotientMap_comp_mk Ideal.le_comap_map
  have hJmap : J.map (algebraMap (R ⧸ I) (Λ ⧸ M)) = N.map qΛ := by
    calc
      J.map f = (K.map qR).map f := by rw [hJI]
      _ = K.map (f.comp qR) := by rw [Ideal.map_map]
      _ = K.map (qΛ.comp (algebraMap R Λ)) := by rw [hf]
      _ = (K.map (algebraMap R Λ)).map qΛ := by rw [Ideal.map_map]
      _ = N.map qΛ := rfl
  let eΛ₀ : ((Λ ⧸ M) ⧸ J.map (algebraMap (R ⧸ I) (Λ ⧸ M))) ≃+* ((Λ ⧸ M) ⧸ N.map qΛ) :=
    Ideal.quotientEquivAlgOfEq (Λ ⧸ M) hJmap
  let eΛ' := eΛ₀.trans eΛ
  have he : ∀ x : (R ⧸ I) ⧸ J,
      eΛ' (algebraMap ((R ⧸ I) ⧸ J) ((Λ ⧸ M) ⧸ J.map (algebraMap (R ⧸ I) (Λ ⧸ M))) x) =
        algebraMap (R ⧸ K) (Λ ⧸ N) (eR x) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    show eΛ' (Ideal.Quotient.mk _ (f (Ideal.Quotient.mk I r))) =
      algebraMap (R ⧸ K) (Λ ⧸ N) (eR (Ideal.Quotient.mk J (Ideal.Quotient.mk I r)))
    have hfr : f (Ideal.Quotient.mk I r) = qΛ (algebraMap R Λ r) := by
      simpa [RingHom.comp_apply, f, qR, qΛ] using
        congrArg (fun g : R →+* Λ ⧸ M => g r) hf
    rw [hfr]
    show eΛ (eΛ₀ (Ideal.Quotient.mk _ (qΛ (algebraMap R Λ r)))) =
      Ideal.Quotient.mk N (algebraMap R Λ r)
    simp only [eΛ₀]
    exact DoubleQuot.quotQuotEquivQuotOfLE_quotQuotMk (algebraMap R Λ r) hMN
  refine indSmooth_of_ringEquiv _ _ _ _ eR.symm eΛ'.symm (fun r => ?_) hPTK
  simpa using (congrArg eΛ'.symm (he (eR.symm r))).symm

private theorem exists_reduced_maximal_bad_quotient
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Λ : Type u) [CommRing Λ] [Algebra R Λ] [IsNoetherianRing Λ]
    (hregular : IsRegularRingMap R Λ) (hfail : ¬ IndSmooth R Λ) :
    ∃ I : Ideal R, ¬ IndSmooth (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) ∧
      IsReduced (R ⧸ I) ∧
      IsRegularRingMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) ∧
      (∀ J : Ideal (R ⧸ I), J ≠ ⊥ →
        IndSmooth ((R ⧸ I) ⧸ J)
          ((Λ ⧸ I.map (algebraMap R Λ)) ⧸
            J.map (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))) := by
  have hPbot : ¬ IndSmooth (R ⧸ (⊥ : Ideal R)) (Λ ⧸ (⊥ : Ideal R).map (algebraMap R Λ)) := by
    intro hPT0
    let : Module.Flat R Λ := hregular.1
    exact hfail (ind_smooth_of_isNilpotent (R := R) (Λ := Λ) ⊥ ⟨1, by simp⟩ hPT0)
  obtain ⟨I, hPI, hmax⟩ := exists_maximal_ideal_property R
    (fun I => ¬ IndSmooth (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) ⟨⊥, hPbot⟩
  let : Algebra (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hregular₀ : IsRegularRingMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) :=
    regularRingMap_quotient R Λ I hregular
  have hquot : ∀ J : Ideal (R ⧸ I), J ≠ ⊥ →
      IndSmooth ((R ⧸ I) ⧸ J)
        ((Λ ⧸ I.map (algebraMap R Λ)) ⧸
          J.map (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)))) :=
    fun J hJ => indSmooth_quotient_of_maximal_bad R Λ I
      (fun K hIK => Classical.byContradiction (hmax K · hIK)) J hJ
  exact ⟨I, hPI, isReduced_of_indSmooth_on_nonzero_quotients _ _ hregular₀.1 hPI hquot,
    hregular₀, hquot⟩

end MaximalFailure

section TotalFractionRing

private noncomputable def residueField_algEquiv_localizationAtPrime
    (R : Type u) [CommRing R] [IsReduced R] (p : Ideal R) [p.IsPrime]
    (hp : p ∈ minimalPrimes R) : p.ResidueField ≃ₐ[R] Localization.AtPrime p := by
  let K := Localization.AtPrime p
  letI : Field K := (isField_localizationAtPrime_of_minimal R p hp).toField
  let e : p.ResidueField ≃ₐ[K] K :=
    (Ideal.quotientEquivAlgOfEq K (IsLocalRing.maximalIdeal_eq_bot (R := K))).trans
      (AlgEquiv.quotientBot K K)
  exact AlgEquiv.ofRingEquiv (f := e.toRingEquiv) (by
    intro r
    change e (algebraMap K p.ResidueField (algebraMap R K r)) = algebraMap R K r
    exact e.commutes (algebraMap R K r))

/-- The total ring of fractions of a reduced Noetherian ring is a finite product of fields, one
for each minimal prime (Lemmas `02LX` and `00FR`). -/
@[ega "II 6.4.7"]
private theorem reduced_totalFractionRing_is_finite_product
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R] :
    ∃ (n : ℕ) (q : Fin n → Ideal R), ∃ hmin : ∀ i, q i ∈ minimalPrimes R,
      Function.Injective q ∧ (∀ p, p ∈ minimalPrimes R → ∃ i, q i = p) ∧
        Nonempty (FractionRing R ≃ₐ[R]
          (∀ i, @Ideal.ResidueField R _ (q i) (hmin i).left.left)) := by
  classical
  let : Finite (minimalPrimes R) := (minimalPrimes.finite_of_isNoetherianRing (R := R)).to_subtype
  let : Fintype (minimalPrimes R) := Fintype.ofFinite _
  let e := Fintype.equivFin (minimalPrimes R)
  let q : Fin (Fintype.card (minimalPrimes R)) → Ideal R := fun i => (e.symm i).val
  have hmin : ∀ i, q i ∈ minimalPrimes R := fun i => (e.symm i).property
  let : ∀ i, (q i).IsPrime := fun i => (hmin i).left.left
  have hinj : Function.Injective q := fun i j hij =>
    e.symm.injective (Subtype.ext hij)
  have hsurj : ∀ p, p ∈ minimalPrimes R → ∃ i, q i = p := fun p hp => ⟨e ⟨p, hp⟩, by simp [q]⟩
  have hzd : zeroDivisorsSet R = ⋃ i, (q i : Set R) := by
    have hzero : zeroDivisorsSet R = zeroDivisorSet R := by
      ext x
      rw [mem_zeroDivisorsSet_iff]
      rfl
    rw [hzero, ← iUnion_minimalPrimes_eq_zeroDivisors R]
    ext x
    simp only [Set.mem_iUnion]
    refine ⟨fun ⟨p, hp, hx⟩ => ?_, fun ⟨i, hi⟩ => ⟨q i, hmin i, hi⟩⟩
    obtain ⟨i, rfl⟩ := hsurj p hp
    exact ⟨i, hx⟩
  have hprod := total_fraction_ring_isoProd_localization_atPrime _ q hmin hinj hzd
  let ePi : (∀ i, @Localization.AtPrime R _ (q i) (hmin i).left.left) ≃ₐ[R]
      (∀ i, @Ideal.ResidueField R _ (q i) (hmin i).left.left) :=
    AlgEquiv.piCongrRight fun i =>
      (residueField_algEquiv_localizationAtPrime R (q i) (hmin i)).symm
  exact ⟨_, q, hmin, hinj, hsurj, hprod.map fun e => e.trans ePi⟩

/-- PT holds after inverting the nonzerodivisors of a reduced Noetherian base: the total ring of
fractions is a finite product of residue fields at the minimal primes, each fibre is again a
regular map of Noetherian rings (Lemma `07C1`), so the field case applies factorwise and
Lemma `07F3` assembles the product. -/
private theorem indSmooth_totalFractionRing_of_field_case
    (hfield : ∀ (k : Type u) [Field k] (Λ : Type u) [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ], IsRegularRingMap k Λ → IndSmooth k Λ)
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (Λ : Type u) [CommRing Λ] [Algebra R Λ] [IsNoetherianRing Λ]
    (hregular : IsRegularRingMap R Λ) :
    IndSmooth (FractionRing R) (FractionRing R ⊗[R] Λ) := by
  classical
  obtain ⟨n, q, hmin, hqinj, hqsurj, ⟨eR⟩⟩ := reduced_totalFractionRing_is_finite_product R
  let : ∀ i, (q i).IsPrime := fun i => (hmin i).left.left
  let K : Fin n → Type u := fun i => (q i).ResidueField
  let L : Fin n → Type u := fun i => (q i).Fiber Λ
  let : ∀ i, Field (K i) := fun _ => inferInstance
  let : ∀ i, CommRing (L i) := fun _ => inferInstance
  let : ∀ i, Algebra (K i) (L i) := fun _ => inferInstance
  let : ∀ i, Algebra Λ (L i) := fun _ => Algebra.TensorProduct.rightAlgebra
  let : ∀ i, IsNoetherianRing (L i) := fun i => (q i).isNoetherianRing_fiber Λ
  have hptProd : IndSmooth (∀ i, K i) (∀ i, L i) :=
    indSmooth_pi_fin n K L fun i => hfield (K i) (L i) (regularRingMap_residueFiber R Λ (q i)
      hregular)
  let e₁ := Algebra.TensorProduct.congr eR (AlgEquiv.refl : Λ ≃ₐ[R] Λ)
  let eA : (FractionRing R ⊗[R] Λ) ≃+* (∀ i, L i) :=
    e₁.toRingEquiv.trans
      ((Algebra.TensorProduct.comm R (∀ i, K i) Λ).toRingEquiv.trans
        ((Algebra.TensorProduct.piRight R Λ Λ K).toRingEquiv.trans
          (RingEquiv.piCongrRight fun i => (Algebra.TensorProduct.comm R Λ (K i)).toRingEquiv)))
  have he : ∀ x : FractionRing R,
      eA (algebraMap (FractionRing R) (FractionRing R ⊗[R] Λ) x) =
        algebraMap (∀ i, K i) (∀ i, L i) (eR x) := by
    intro x
    funext i
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      RingEquiv.coe_trans, RingEquiv.coe_mk, AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      Function.comp_apply, Algebra.TensorProduct.congr_apply, AlgEquiv.refl_toAlgHom,
      Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgHom.coe_id, id_eq,
      Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.piRight_tmul,
      RingEquiv.piCongrRight_apply, eA, e₁]
    show eR x i ⊗ₜ[R] (1 : Λ) = algebraMap (K i) (L i) (eR x i)
    rw [Algebra.TensorProduct.algebraMap_apply]
    rfl
  have he' : ∀ x : (∀ i, K i),
      eA.symm (algebraMap (∀ i, K i) (∀ i, L i) x) =
        algebraMap (FractionRing R) (FractionRing R ⊗[R] Λ) (eR.symm x) := by
    intro x
    apply eA.injective
    rw [RingEquiv.apply_symm_apply, he (eR.symm x)]
    simp
  let : Algebra (FractionRing R) (FractionRing R ⊗[R] Λ) := Algebra.TensorProduct.leftAlgebra
  exact indSmooth_of_ringEquiv (∀ i, K i) (FractionRing R) (∀ i, L i)
    (FractionRing R ⊗[R] Λ) eR.symm eA.symm he' hptProd

end TotalFractionRing

section StrictlyStandard

/-- If multiplication by `x` is cancellative, then `z * x ^ m = 0 ↔ z * x ^ n = 0` for `m ≤ n`. -/
private theorem mul_pow_eq_zero_iff_of_le {M : Type*} [MonoidWithZero M] {x : M}
    (hx : ∀ z, z * x = 0 → z = 0) {m n : ℕ} (hmn : m ≤ n) (z : M) :
    z * x ^ m = 0 ↔ z * x ^ n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hk : ∀ (k : ℕ) (w : M), w * x ^ k = 0 → w = 0 := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih => exact fun w hw => ih w (hx _ (by simpa [pow_succ, mul_assoc] using hw))
  refine ⟨fun h => by rw [pow_add, ← mul_assoc, h, zero_mul], fun h => hk k _ ?_⟩
  rwa [mul_assoc, ← pow_add]

/-- If multiplication by `x` is cancellative, then `x` and `x ^ 2` have the same annihilator. -/
private theorem annihilator_span_singleton_eq_pow_two {M : Type*} [CommRing M] {x : M}
    (hx : ∀ z, z * x = 0 → z = 0) :
    (Submodule.span M {x}).annihilator = (Submodule.span M {x ^ 2}).annihilator := by
  ext z
  rw [Submodule.mem_annihilator_span_singleton, Submodule.mem_annihilator_span_singleton,
    smul_eq_mul, smul_eq_mul]
  simpa using mul_pow_eq_zero_iff_of_le hx (m := 1) (n := 2) (by norm_num) z

/-- Given a strictly standard nonzerodivisor `π` in a finitely presented `R`-algebra `B` mapping
to `Λ`, PT modulo every nonzero ideal produces a smooth factorization of `B → Λ`: PT modulo `π⁸`
gives a smooth algebra there, Lemma `07CP` descends it to a smooth `R`-algebra `D` factorizing
modulo `π⁴`, and Lemma `07CT` merges `B` and `D` into a finitely presented `R`-algebra whose
singular ideal is the unit ideal. -/
private theorem exists_smooth_factorization_of_strictlyStandard
    (R : Type u) (Λ : Type u) (B : Type u)
    [CommRing R] [CommRing Λ] [CommRing B] [IsNoetherianRing R] [Nontrivial R]
    [Algebra R Λ] [Algebra R B] [Algebra B Λ] [IsScalarTower R B Λ]
    [Algebra.FinitePresentation R B]
    (s : nonZeroDivisors R)
    (hstrict : IsStrictlyStandard (R := R) (A := B) (algebraMap R B s.1))
    (hflat : Module.Flat R Λ)
    (hquot : ∀ I : Ideal R, I ≠ ⊥ → IndSmooth (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) :
    ∃ (E : Type u) (_ : CommRing E) (algE : Algebra R E),
      letI := algE
      Algebra.FinitePresentation R E ∧ ∃ (bToE : B →ₐ[R] E) (gE : E →ₐ[R] Λ),
        gE.comp bToE = (Algebra.ofId B Λ).restrictScalars R ∧ Algebra.Smooth R E := by
  let π : R := s.1
  let : Module.Flat R Λ := hflat
  have hπcancel : ∀ z : Λ, z * algebraMap R Λ π = 0 → z = 0 := by
    intro z hz
    have hinj : Function.Injective (fun x : Λ => (π : R) • x) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Λ) s.property
    apply hinj
    simp [Algebra.smul_def, hz, mul_comm]
  have hπR : ∀ r : R, r * π = 0 → r = 0 := fun r hr =>
    mem_nonZeroDivisors_iff_right.mp s.property r hr
  let I8 : Ideal R := Ideal.span {π ^ 8}
  have hI8 : I8 ≠ ⊥ := fun h =>
    nonZeroDivisors.ne_zero (pow_mem s.property 8) (Ideal.span_singleton_eq_bot.mp h)
  let R8 := R ⧸ I8
  let Λ8 := Λ ⧸ I8.map (algebraMap R Λ)
  have hPT8 : IndSmooth R8 Λ8 := hquot I8 hI8
  have hmapI8 : I8.map (algebraMap R Λ) = Ideal.span {(algebraMap R Λ π) ^ 8} := by
    show Ideal.map (algebraMap R Λ) (Ideal.span {π ^ 8}) = _
    simp [Ideal.map_span, map_pow]
  let : Algebra R8 Λ8 := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R R8 Λ8 := IsScalarTower.of_algebraMap_eq' (by
    ext r
    simp [R8, Λ8, Ideal.Quotient.algebraMap_eq])
  let B8 := R8 ⊗[R] B
  let : Algebra R8 B8 := Algebra.TensorProduct.leftAlgebra
  let : Algebra B B8 := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R B B8 := Algebra.TensorProduct.right_isScalarTower
  let : Algebra.FinitePresentation R8 B8 := inferInstance
  let fΛ8 : Λ →ₐ[R] Λ8 := Ideal.Quotient.mkₐ R (I8.map (algebraMap R Λ))
  let fBΛ : B →ₐ[R] Λ := (Algebra.ofId B Λ).restrictScalars R
  let fB : B →ₐ[R] Λ8 := fΛ8.comp fBΛ
  let fB8 : B8 →ₐ[R8] Λ8 := (AlgHom.liftEquiv R R8 B Λ8) fB
  obtain ⟨C, instC, algC, hCsmoothAlg, gC, fC, hgfC⟩ :=
    (indSmooth_iff_exists_factorization R8 Λ8).mp hPT8 B8 inferInstance inferInstance
      inferInstance fB8
  let := instC
  let := algC
  let : Algebra R C := ((algebraMap R8 C).comp (algebraMap R R8)).toAlgebra
  let : IsScalarTower R R8 C := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FinitePresentation R8 C := hCsmoothAlg.finitePresentation
  let gBC : B →ₐ[R] C := (gC.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := R8) (B := B))
  have hR4 : ∀ r : R, r * π ^ 4 = 0 ↔ r * π ^ 8 = 0 :=
    mul_pow_eq_zero_iff_of_le hπR (by norm_num)
  have hΛ4 : ∀ z : Λ, z * algebraMap R Λ π ^ 4 = 0 ↔ z * algebraMap R Λ π ^ 8 = 0 :=
    mul_pow_eq_zero_iff_of_le hπcancel (by norm_num)
  let J8 : Ideal Λ := Ideal.span {(algebraMap R Λ π) ^ 8}
  let Λ8' := Λ ⧸ J8
  have hI8J : I8.map (algebraMap R Λ) = J8 := hmapI8
  have hI8comap : I8 ≤ J8.comap (algebraMap R Λ) := by
    rw [← hI8J]
    exact Ideal.le_comap_map
  let : Algebra R8 Λ8' := Ideal.Quotient.algebraQuotientOfLEComap hI8comap
  have hquot8 : ∀ r : R, algebraMap R8 Λ8' (Ideal.Quotient.mk I8 r) =
      Ideal.Quotient.mk J8 (algebraMap R Λ r) := by
    intro r
    show Ideal.quotientMap J8 (algebraMap R Λ) hI8comap (Ideal.Quotient.mk I8 r) = _
    rw [Ideal.quotientMap_mk]
  let : IsScalarTower R Λ Λ8' := Ideal.Quotient.isScalarTower R Λ J8
  let : IsScalarTower R R8 Λ8' := IsScalarTower.of_algebraMap_eq fun r => by
    calc
      algebraMap R Λ8' r = algebraMap Λ Λ8' (algebraMap R Λ r) :=
        IsScalarTower.algebraMap_apply R Λ Λ8' r
      _ = algebraMap R8 Λ8' (algebraMap R R8 r) := by
        simpa only [← Ideal.Quotient.algebraMap_eq] using (hquot8 r).symm
  let eΛ8R : Λ8 ≃ₐ[R] Λ8' := Ideal.quotientEquivAlgOfEq R hmapI8
  let eΛ8 : Λ8 ≃ₐ[R8] Λ8' :=
    { toRingEquiv := eΛ8R.toRingEquiv
      commutes' := by
        intro x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
        show eΛ8R (algebraMap R8 Λ8 (algebraMap R R8 r)) = algebraMap R8 Λ8' (algebraMap R R8 r)
        calc
          eΛ8R (algebraMap R8 Λ8 (algebraMap R R8 r)) = eΛ8R (algebraMap R Λ8 r) := by
            rw [← IsScalarTower.algebraMap_apply R R8 Λ8 r]
          _ = algebraMap R Λ8' r := eΛ8R.commutes r
          _ = algebraMap R8 Λ8' (algebraMap R R8 r) :=
            IsScalarTower.algebraMap_apply R R8 Λ8' r }
  let fC' : C →ₐ[R8] Λ8' := eΛ8.toAlgHom.comp fC
  have hLift := @exists_finitePresentation_lift_smoothAt R Λ C _ _ _ _ _ (π ^ 4)
  rw [← pow_mul, map_pow, ← pow_mul] at hLift
  obtain ⟨D, hDcomm, hDalg, hDfp, hD⟩ := hLift hR4 hΛ4 hquot8 fC'
  let : CommRing D := hDcomm
  let : Algebra R D := hDalg
  let : Algebra.FinitePresentation R D := hDfp
  rw [map_pow] at hD
  obtain ⟨gD, cD, reduceΛ, reduceD, -,
    hReduceΛ, hReduceD, hcD, hcR, -, hDaway, hDover, -⟩ := hD
  let I_B4 : Ideal B := Ideal.span {(algebraMap R B π) ^ 4}
  let I_D4 : Ideal D := Ideal.span {(algebraMap R D π) ^ 4}
  let I_Λ4 : Ideal Λ := Ideal.span {(algebraMap R Λ π) ^ 4}
  let D4 := D ⧸ I_D4
  let fBD4 : B →ₐ[R] D4 :=
    { toRingHom := cD.comp gBC.toRingHom
      commutes' := by
        intro r
        show cD (gBC (algebraMap R B r)) = algebraMap R D4 r
        calc
          cD (gBC (algebraMap R B r)) = cD (algebraMap R C r) := by rw [gBC.commutes]
          _ = cD (algebraMap R8 C (Ideal.Quotient.mk I8 r)) := by
            rw [IsScalarTower.algebraMap_apply R R8 C r]
            rfl
          _ = Ideal.Quotient.mk I_D4 (algebraMap R D r) := hcR r
          _ = algebraMap R D4 r := rfl }
  have hkerBD4 : I_B4 ≤ RingHom.ker fBD4.toRingHom := by
    show Ideal.span {(algebraMap R B π) ^ 4} ≤ _
    rw [Ideal.span_le]
    rintro x ⟨rfl⟩
    show fBD4 ((algebraMap R B π) ^ 4) = 0
    rw [map_pow, fBD4.commutes]
    show (Ideal.Quotient.mk I_D4 (algebraMap R D π)) ^ 4 = 0
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  let bar : (B ⧸ I_B4) →ₐ[R] D4 := Ideal.Quotient.liftₐ I_B4 fBD4 hkerBD4
  have hCfactor' (b : B) : fC' (gBC b) = Ideal.Quotient.mk J8 (fBΛ b) := by
    have hCfactor : fC (gC (Algebra.TensorProduct.includeRight b)) = fB8
        (Algebra.TensorProduct.includeRight b) :=
      congrArg (fun m => m (Algebra.TensorProduct.includeRight b)) hgfC
    calc
      fC' (gBC b) = eΛ8 (fC (gC (Algebra.TensorProduct.includeRight b))) := rfl
      _ = eΛ8 (fB b) := by
        rw [hCfactor]
        exact congrArg eΛ8 ((AlgHom.liftEquiv_tmul fB 1 b).trans (one_smul _ _))
      _ = Ideal.Quotient.mk J8 (fBΛ b) := by
        show eΛ8R (Ideal.Quotient.mk (I8.map (algebraMap R Λ)) (fBΛ b)) = _
        exact Ideal.quotientEquivAlgOfEq_mk R hmapI8 (fBΛ b)
  have hcompat (b : B) : reduceD (cD (gBC b)) = Ideal.Quotient.mk I_Λ4 (fBΛ b) := by
    calc
      reduceD (cD (gBC b)) = reduceΛ (fC' (gBC b)) := hcD (gBC b)
      _ = reduceΛ (Ideal.Quotient.mk J8 (fBΛ b)) := congrArg reduceΛ (hCfactor' b)
      _ = Ideal.Quotient.mk I_Λ4 (fBΛ b) := hReduceΛ (fBΛ b)
  have hbar' : ∀ (a : B) (y : D),
      bar (Ideal.Quotient.mk I_B4 a) = Ideal.Quotient.mk I_D4 y →
        Ideal.Quotient.mk I_Λ4 (fBΛ a) = Ideal.Quotient.mk I_Λ4 (gD y) := by
    intro a y hay
    have h0 : reduceD (bar (Ideal.Quotient.mk I_B4 a)) = Ideal.Quotient.mk I_Λ4 (fBΛ a) := by
      show reduceD (cD (gBC a)) = _
      exact hcompat a
    rw [hay, hReduceD] at h0
    exact h0.symm
  obtain ⟨E, hEcomm, hER, hEalg, hEtower, hEfp, bToE, gE, hcompB, -, hsingular⟩ :=
    exists_finitePresentation_factorization_singularIdeal_le R B D Λ π
      (annihilator_span_singleton_eq_pow_two hπR) (annihilator_span_singleton_eq_pow_two hπcancel)
      fBΛ gD hstrict
      bar hbar'
  let : CommRing E := hEcomm
  let : Algebra D E := hER
  let : Algebra R E := hEalg
  let : IsScalarTower R D E := hEtower
  let : Algebra.FinitePresentation R E := hEfp
  have hDsmoothAt (q : Ideal D) [q.IsPrime] : Algebra.SmoothAt R D q := by
    have hlocal : Algebra.IsSmoothAt R q := by
      by_cases hq : (algebraMap R D π) ^ 4 ∈ q
      · have hIle : I_D4 ≤ q := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hq)
        let qbar : Ideal D4 := q.map (Ideal.Quotient.mk I_D4)
        have : qbar.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hIle
        let p : Ideal C := qbar.comap cD
        have : p.IsPrime := Ideal.comap_isPrime cD qbar
        have : Algebra.Smooth R8 C := hCsmoothAlg
        exact hDover q hq ⟨p, inferInstance,
          Algebra.FormallySmooth.comp R8 C (Localization.AtPrime p), rfl⟩
      · exact hDaway q hq
    exact Algebra.IsSmoothAt.exists_notMem_smooth R q
  have hsingD : Stacks.Smoothing.singularIdeal R D = ⊤ := by
    simp [Stacks.Smoothing.singularIdeal, hDsmoothAt]
  have hsingE : Stacks.Smoothing.singularIdeal R E = ⊤ := by
    apply top_unique
    simpa only [hsingD, Ideal.map_top] using hsingular.2
  have hEsmooth : Algebra.Smooth R E := by
    refine (Algebra.smooth_iff_forall_exists_notMem_smooth R E).2 fun q hq => ?_
    have hEall : Algebra.SmoothAt R E q := by
      by_contra hns
      have hmem : (⟨q, hq⟩ : PrimeSpectrum E) ∈ PrimeSpectrum.zeroLocus
          (Stacks.Smoothing.singularIdeal R E : Set E) := by
        rw [Stacks.Smoothing.zeroLocus_singularIdeal]
        exact hns
      rw [hsingE] at hmem
      simp at hmem
    obtain ⟨g, hg, hgsmooth⟩ := (Algebra.smoothAt_iff R E q).mp hEall
    exact ⟨g, hg, hgsmooth⟩
  exact ⟨E, hEcomm, hEalg, hEfp, bToE, gE, hcompB, hEsmooth⟩

end StrictlyStandard

section Main

/-- Elements of a submonoid `S` of `R` become units in the localization of an `R`-algebra `M`
at the image of `S`. -/
private theorem isUnit_algebraMap_localization_map (R M : Type u) [CommRing R] [CommRing M]
    [Algebra R M] (S : Submonoid R) (s : S) :
    IsUnit (algebraMap R (Localization (S.map (algebraMap R M))) s.1) := by
  rw [IsScalarTower.algebraMap_eq R M]
  exact IsLocalization.map_units (M := S.map (algebraMap R M)) _
    ⟨algebraMap R M s.1, Submonoid.mem_map.mpr ⟨s.1, s.2, rfl⟩⟩

/-- The inductive step: a reduced base whose every nonzero quotient satisfies PT satisfies PT. -/
private theorem indSmooth_of_field_case_of_isReduced
    (hfield : ∀ (k : Type u) [Field k] (Λ : Type u) [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ], IsRegularRingMap k Λ → IndSmooth k Λ)
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (Λ : Type u) [CommRing Λ] [Algebra R Λ] [IsNoetherianRing Λ]
    (hregular : IsRegularRingMap R Λ) (hbad : ¬ IndSmooth R Λ)
    (hquot : ∀ I : Ideal R, I ≠ ⊥ → IndSmooth (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) :
    IndSmooth R Λ := by
  rw [indSmooth_iff_exists_factorization]
  intro A instA algA hAfp fA
  let := algA
  let : Algebra.FinitePresentation R A := hAfp
  let S : Submonoid R := nonZeroDivisors R
  let Q := Localization S
  let A_Q := Q ⊗[R] A
  let Λ_Q := Q ⊗[R] Λ
  let : Algebra Q A_Q := Algebra.TensorProduct.leftAlgebra
  let : Algebra Q Λ_Q := Algebra.TensorProduct.leftAlgebra
  let fQ : A_Q →ₐ[Q] Λ_Q := Algebra.TensorProduct.map (AlgHom.id Q Q) fA
  have hPTQ : IndSmooth Q Λ_Q := indSmooth_totalFractionRing_of_field_case hfield R Λ hregular
  have : Algebra.FinitePresentation Q A_Q := Algebra.FinitePresentation.baseChange Q
  obtain ⟨B', instB', algB', hBsmoothAlg, gQ', hQ', hcompQ'⟩ :=
    (indSmooth_iff_exists_factorization Q Λ_Q).mp hPTQ A_Q inferInstance inferInstance
      inferInstance fQ
  let := instB'
  let := algB'
  let AS := Localization (S.map (algebraMap R A))
  let ΛS := Localization (S.map (algebraMap R Λ))
  have hΛUnits := isUnit_algebraMap_localization_map R Λ S
  let : Algebra Q ΛS := (IsLocalization.lift
    (M := S) (S := Q) (P := ΛS) (g := algebraMap R ΛS) hΛUnits).toAlgebra
  let : IsScalarTower R Q ΛS := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.lift_comp hΛUnits).symm
  let eQL : Λ_Q ≃ₐ[Q] ΛS := Localization.tensorRightAlgEquiv S Λ
  have hqUnits := isUnit_algebraMap_localization_map R A S
  let : Algebra Q AS := (IsLocalization.lift
    (M := S) (S := Q) (P := AS) (g := algebraMap R AS) hqUnits).toAlgebra
  let : IsScalarTower R Q AS := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.lift_comp hqUnits).symm
  let : Algebra R B' := ((algebraMap Q B').comp (algebraMap R Q)).toAlgebra
  let : IsScalarTower R Q B' := IsScalarTower.of_algebraMap_eq' rfl
  let gA : A →ₐ[R] B' := (gQ'.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := Q) (B := A))
  have hincl (r : R) : (Algebra.TensorProduct.includeRight (R := R) (A := Q) (B := A))
      (algebraMap R A r) = algebraMap Q A_Q (algebraMap R Q r) := by
    rw [AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply R Q A_Q r
  have hAunits : ∀ s : S.map (algebraMap R A), IsUnit (gA s.1) := by
    intro s
    obtain ⟨r, hr, hval⟩ := Submonoid.mem_map.mp s.2
    rw [← hval]
    show IsUnit (gQ' ((Algebra.TensorProduct.includeRight (R := R) (A := Q) (B := A))
      (algebraMap R A r)))
    rw [hincl r, gQ'.commutes]
    exact IsUnit.map (algebraMap Q B') (IsLocalization.map_units Q ⟨r, hr⟩)
  let gAS : AS →+* B' := IsLocalization.lift
    (M := S.map (algebraMap R A)) (S := AS) (P := B') (g := gA.toRingHom) hAunits
  let : Algebra AS B' := gAS.toAlgebra
  let : Algebra A B' := gA.toRingHom.toAlgebra
  let : IsScalarTower A AS B' := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.lift_comp hAunits).symm
  let : IsScalarTower R AS B' := IsScalarTower.of_algebraMap_eq' (by
    ext r
    show algebraMap R B' r = algebraMap AS B' (algebraMap R AS r)
    rw [IsScalarTower.algebraMap_apply R A AS r]
    show algebraMap R B' r = gAS (algebraMap A AS (algebraMap R A r))
    rw [← gA.commutes r]
    exact (congrArg (fun f : A →+* B' => f (algebraMap R A r))
      (IsLocalization.lift_comp hAunits)).symm)
  let : IsScalarTower Q AS B' := IsScalarTower.of_algebraMap_eq' (by
    apply IsLocalization.ringHom_ext S
    ext r
    show algebraMap Q B' (algebraMap R Q r) =
      algebraMap AS B' (algebraMap Q AS (algebraMap R Q r))
    calc
      algebraMap Q B' (algebraMap R Q r) = algebraMap R B' r :=
        (IsScalarTower.algebraMap_apply R Q B' r).symm
      _ = algebraMap AS B' (algebraMap R AS r) := IsScalarTower.algebraMap_apply R AS B' r
      _ = algebraMap AS B' (algebraMap Q AS (algebraMap R Q r)) := by
        rw [IsScalarTower.algebraMap_apply R Q AS r])
  let hΛS : B' →ₐ[Q] ΛS := eQL.toAlgHom.comp hQ'
  let : Algebra B' ΛS := hΛS.toRingHom.toAlgebra
  let : IsScalarTower Q B' ΛS := IsScalarTower.of_algebraMap_eq' (by
    ext q
    exact (hΛS.commutes q).symm)
  let : Algebra AS ΛS := (hΛS.toRingHom.comp gAS).toAlgebra
  let : IsScalarTower AS B' ΛS := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A Λ := fA.toRingHom.toAlgebra
  let : IsScalarTower R A Λ := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact (fA.commutes r).symm)
  let : Algebra A ΛS := ((algebraMap Λ ΛS).comp (algebraMap A Λ)).toAlgebra
  let : IsScalarTower A Λ ΛS := inferInstance
  have hfactorLoc : ∀ a : A, hΛS (gA a) = algebraMap Λ ΛS (fA a) := by
    intro a
    calc
      hΛS (gA a) = eQL (hQ' (gQ' (Algebra.TensorProduct.includeRight a))) := rfl
      _ = eQL (fQ (Algebra.TensorProduct.includeRight a)) :=
          congrArg eQL (DFunLike.congr_fun hcompQ' _)
      _ = eQL ((1 : Q) ⊗ₜ[R] fA a) := by
          refine congrArg eQL ?_
          show Algebra.TensorProduct.map (AlgHom.id Q Q) fA ((1 : Q) ⊗ₜ[R] a) = _
          simp
      _ = algebraMap Λ ΛS (fA a) :=
          Localization.tensorRightAlgEquiv_apply_one_tmul (M := S) (x := fA a)
  let : IsScalarTower A B' ΛS := IsScalarTower.of_algebraMap_smul fun a z ↦ by
    calc
      algebraMap B' ΛS (algebraMap A B' a) • z = hΛS (gA a) • z := rfl
      _ = algebraMap Λ ΛS (fA a) • z := congrArg (fun x : ΛS ↦ x • z) (hfactorLoc a)
      _ = a • z := by
        calc
          algebraMap Λ ΛS (fA a) • z = fA a • z :=
            IsScalarTower.algebraMap_smul (R := Λ) (A := ΛS) (M := ΛS) (r := fA a) (x := z)
          _ = a • z := by
            show algebraMap A Λ a • z = a • z
            exact IsScalarTower.algebraMap_smul (R := A) (A := Λ) (M := ΛS) (r := a) (x := z)
  obtain ⟨B, hCommB, hAlgAB, hAlgBΛ, hAlgRB, hRAB, hABΛ, hRBΛ, ⟨sπ, hElem⟩⟩ :=
    exists_factorization_isElementaryStandard R A Λ S ⟨B', inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, hBsmoothAlg⟩
  let : CommRing B := hCommB
  let : Algebra A B := hAlgAB
  let : Algebra B Λ := hAlgBΛ
  let : Algebra R B := hAlgRB
  let : IsScalarTower R A B := hRAB
  let : IsScalarTower A B Λ := hABΛ
  let : IsScalarTower R B Λ := hRBΛ
  let π : R := sπ.1
  have hElemKeep : IsElementaryStandard (R := R) (A := B) (algebraMap R B π) := hElem
  obtain ⟨P, c, hcn, hcm, -⟩ := hElem
  have hFPB : Algebra.FinitePresentation R B := by
    have hfg : (Ideal.span (Set.range P.f)).FG := Submodule.fg_span (Set.finite_range P.f)
    let : Algebra.FinitePresentation R
        (MvPolynomial (Fin P.n) R ⧸ Ideal.span (Set.range P.f)) :=
      Algebra.FinitePresentation.quotient hfg
    exact Algebra.FinitePresentation.equiv P.iso.symm
  let : Algebra.FinitePresentation R B := hFPB
  have hstrict : IsStrictlyStandard (R := R) (A := B) (algebraMap R B π) :=
    elementaryStandard_implies_strictlyStandard
      (⟨R, B, algebraMap R B π⟩ : SixStandardnessConditions) hElemKeep
  have hRnontrivial : Nontrivial R := by
    by_contra hnt
    let : Subsingleton R := not_nontrivial_iff_subsingleton.mp hnt
    let : Subsingleton Λ := Algebra.subsingleton R Λ
    exact hbad (indSmooth_of_smooth R Λ (RingHom.smooth_algebraMap.mp
      (RingHom.Smooth.of_bijective
        ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩)))
  let : Nontrivial R := hRnontrivial
  obtain ⟨E, hEcomm, hEalg, hEfp, bToE, gE, hcompB, hEsmooth⟩ :=
    exists_smooth_factorization_of_strictlyStandard R Λ B sπ hstrict hregular.1 hquot
  let : CommRing E := hEcomm
  let : Algebra R E := hEalg
  let aToB : A →ₐ[R] B := (Algebra.ofId A B).restrictScalars R
  have hAtoBfactor : ((Algebra.ofId B Λ).restrictScalars R).comp aToB = fA :=
    AlgHom.ext fun a ↦ (IsScalarTower.algebraMap_apply A B Λ a).symm
  have hfactor : gE.comp (bToE.comp aToB) = fA := by
    rw [← AlgHom.comp_assoc, hcompB, hAtoBfactor]
  exact ⟨E, hEcomm, hEalg, hEsmooth, bToE.comp aToB, gE, hfactor⟩

/-- **Stacks 07F5.** If property PT — that `Λ` is a filtered colimit of smooth `R`-algebras —
holds for every regular ring map `R → Λ` of Noetherian rings whose source is a field, then it
holds for every regular ring map of Noetherian rings. -/
@[stacks 07F5 "Situation 07F2 is `IsRegularRingMap` plus the Noetherian hypotheses, and PT is
`IndSmooth`, the `ObjectProperty.ind` spelling of Lemma 07C3."]
theorem indSmooth_of_indSmooth_of_field_base
    (hfield : ∀ (k : Type u) [Field k] (Λ : Type u) [CommRing Λ] [Algebra k Λ]
      [IsNoetherianRing Λ], IsRegularRingMap k Λ → IndSmooth k Λ)
    (R : Type u) [CommRing R] (Λ : Type u) [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R] [IsNoetherianRing Λ] (hregular : IsRegularRingMap R Λ) :
    IndSmooth R Λ := by
  by_contra hfail
  obtain ⟨I, hbad, hred, hregular₀, hquot⟩ :=
    exists_reduced_maximal_bad_quotient R Λ hregular hfail
  let : Algebra (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsReduced (R ⧸ I) := hred
  exact hbad (indSmooth_of_field_case_of_isReduced hfield (R ⧸ I)
    (Λ ⧸ I.map (algebraMap R Λ)) hregular₀ hbad hquot)

end Main

end Stacks.Smoothing

end
