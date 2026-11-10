module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.Basic
public import StacksFrontier.RingTheory.Fitting.Basic

/-!
# Fitting ideals and étale localizations

Let `C` be a finite locally free algebra over `A` and let `J` be an ideal of `C`. After
localizing `C` at an element where it becomes étale over `A`, the zeroth Fitting ideal of
`C ⧸ J` becomes a multiple of the localized `J`. Pushing this through a presentation of a
general étale algebra as a standard étale one lets a finitely generated ideal of an étale
`A`-algebra `B` be factored, near any prime of `B`, as the extension of a finitely generated
ideal of `A` times another finitely generated ideal.

## Main results

* `fittingIdealZero_quotient_fg`: the zeroth Fitting ideal of a quotient of a finite
  projective algebra by a finitely generated ideal is finitely generated.
* `map_fittingIdealZero_quotient_eq_mul_of_etale_away`: the localized Fitting ideal is a
  multiple of the localized defining ideal.
* `exists_ideal_map_eq_mul_after_localization`: an ideal of an étale algebra descends, after
  a principal localization, to a product involving an ideal of the base.

## Implementation notes

The zeroth Fitting ideal is `fittingIdeal` from Tag 07Z9 evaluated at `0`. Finite locally
free is represented by finite projective; the results do not depend on the locally constant
rank, so no rank is fixed. The finite-generation assertion about the Fitting ideal, which
does not involve the localization, is stated separately from the existence of the factor
ideal.

The inclusions of closed subsets of spectra `V(J) ⊆ V(aB)` and `V(I) ⊆ V(a)` are expressed
algebraically as `algebraMap A B a ∈ J.radical` and `a ∈ I.radical`, their standard
ideal-theoretic form. The extension of `I` to the localization is written using the
composite ring homomorphism in order to make its base ring explicit. The source of Tag 0813
assumes that `a` is a nonzerodivisor, but neither its proof nor its conclusion uses that
assumption, so the statement is given in the stronger form.

## References

* [Stacks Project, Tag 0812](https://stacks.math.columbia.edu/tag/0812)
* [Stacks Project, Tag 0813](https://stacks.math.columbia.edu/tag/0813)
-/

@[expose] public section

universe u v

open scoped TensorProduct

/-- The quotient of a finitely presented ring by a finitely generated ideal is
finitely presented. -/
private theorem finitePresentation_quotient_of_fg
    {R : Type*} {C : Type*} [CommRing R] [CommRing C] [Module R C]
    [IsScalarTower R C C] [Module.FinitePresentation R C] (J : Ideal C) (hJ : J.FG) :
    Module.FinitePresentation R (C ⧸ J) := by
  refine Module.finitePresentation_of_surjective
    ((Submodule.mkQ J).restrictScalars R) (Submodule.mkQ_surjective J) ?_
  rw [LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
  exact Submodule.FG.restrictScalars (R := R) hJ

/-- The zeroth Fitting ideal of a quotient of a finitely presented algebra by a finitely
generated ideal is finitely generated. -/
private theorem fittingIdealZero_quotient_fg_of_finitePresentation
    {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Module R C]
    [IsScalarTower R C C] [Module.FinitePresentation R C] (J : Ideal C) (hJ : J.FG) :
    (fittingIdeal (R := R) (M := C ⧸ J) 0).FG := by
  have := finitePresentation_quotient_of_fg (R := R) J hJ
  exact (fittingIdeal_basic_properties.{u, v, v, u} (R := R) (M := C ⧸ J)).2.2.2.1
    inferInstance 0

/-- **Stacks Project, Tag 0812.** The zeroth Fitting ideal of a quotient of a finite
projective algebra by a finitely generated ideal is finitely generated. -/
@[stacks 0812 "finite generation of the Fitting ideal"]
theorem fittingIdealZero_quotient_fg
    (A : Type u) (C : Type v) [CommRing A] [CommRing C] [Algebra A C]
    [Module.Finite A C] [Module.Projective A C] (J : Ideal C) (hJ : J.FG) :
    (fittingIdeal (R := A) (M := C ⧸ J) 0).FG := by
  have := Module.finitePresentation_of_projective A C
  exact fittingIdealZero_quotient_fg_of_finitePresentation J hJ

/-- A surjective ring map with kernel `I` induces a ring isomorphism from the quotient by `I`
compatible with the quotient map. -/
private theorem exists_ringEquiv_quotient_comp_mk {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (I : Ideal R) (h : RingHom.ker f = I) :
    ∃ e : R ⧸ I ≃+* S, e.toRingHom.comp (Ideal.Quotient.mk I) = f :=
  ⟨(Ideal.quotEquivOfEq h.symm).trans (RingHom.quotientKerEquivOfSurjective hf), by
    ext x
    rw [RingHom.comp_apply]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hf x⟩

/-- If a finitely presented algebra `T` over `L` splits off `L` as the quotient by the
complement of an idempotent, then the zeroth Fitting ideal of any quotient `T ⧸ Q` factors
as the image of `Q` in `L` times the Fitting ideal of the complementary factor. -/
private theorem fittingIdeal_split_quotient
    {L T : Type*} [CommRing L] [CommRing T] [Algebra L T]
    [Module.Finite L T] [Module.FinitePresentation L T]
    (μ : T →ₐ[L] L) (hμ : Function.Surjective μ) (e : T)
    (he : IsIdempotentElem e)
    (hker : RingHom.ker μ.toRingHom = Ideal.span {1 - e}) (Q : Ideal T) :
    ∃ J₀ : Ideal L,
      fittingIdeal (R := L) (M := T ⧸ Q) 0 = Ideal.map μ.toRingHom Q * J₀ ∧
      (Q.FG → J₀.FG) := by
  classical
  let I : Ideal T := Ideal.span {1 - e}
  let D := T ⧸ Ideal.span {e}
  have hmul : (1 - e) * e = 0 := by
    rw [sub_mul, one_mul, he.eq]
    ring
  obtain ⟨q1, hq1⟩ := exists_ringEquiv_quotient_comp_mk μ.toRingHom hμ I hker
  let ψ₀ : T ≃+* (T ⧸ I) × D :=
    (AlgEquiv.prodQuotientOfIsIdempotentElem T he.one_sub he (by ring) hmul).toRingEquiv
  let ψ : T ≃+* L × D := ψ₀.trans (RingEquiv.prodCongr q1 (RingEquiv.refl _))
  have hproj₀ : (RingHom.fst (T ⧸ I) D).comp ψ₀.toRingHom = Ideal.Quotient.mk I := by
    ext x
    change ((AlgEquiv.prodQuotientOfIsIdempotentElem T he.one_sub he (by ring)
      hmul) x).1 = _
    rw [AlgEquiv.prodQuotientOfIsIdempotentElem_apply]
  have hprojD₀ : (RingHom.snd (T ⧸ I) D).comp ψ₀.toRingHom =
      Ideal.Quotient.mk (Ideal.span {e}) := by
    ext x
    change ((AlgEquiv.prodQuotientOfIsIdempotentElem T he.one_sub he (by ring)
      hmul) x).2 = _
    rw [AlgEquiv.prodQuotientOfIsIdempotentElem_apply]
  have hprojD : (RingHom.snd L D).comp ψ.toRingHom =
      Ideal.Quotient.mk (Ideal.span {e}) := by
    ext x
    change (RingHom.snd (T ⧸ I) D) (ψ₀ x) = _
    exact DFunLike.congr_fun hprojD₀ x
  let s : L →+* D := (RingHom.snd L D).comp (ψ.toRingHom.comp (algebraMap L T))
  let : Algebra L D := s.toAlgebra
  have hfirst : (RingHom.fst L D).comp ψ.toRingHom = μ.toRingHom := by
    calc
      (RingHom.fst L D).comp ψ.toRingHom =
          q1.toRingHom.comp ((RingHom.fst (T ⧸ I) D).comp ψ₀.toRingHom) := by
            ext x
            rfl
      _ = μ.toRingHom := by rw [hproj₀, hq1]
  let : Algebra L (L × D) := inferInstance
  let ψA : T ≃ₐ[L] L × D := AlgEquiv.ofRingEquiv (f := ψ) (by
    intro x
    apply Prod.ext
    · change ((RingHom.fst L D).comp ψ.toRingHom) (algebraMap L T x) = x
      rw [hfirst]
      simp
    · rfl)
  let Q' : Ideal (L × D) := Ideal.map ψ.toRingHom Q
  let K : Ideal D := Ideal.map (RingHom.snd L D) Q'
  have hs (r : L) : s r = Ideal.Quotient.mk (Ideal.span {e}) (algebraMap L T r) := by
    change (RingHom.snd L D) (ψ (algebraMap L T r)) = _
    exact DFunLike.congr_fun hprojD (algebraMap L T r)
  have hsmul (r : L) (y : D) : r • y = s r * y := by
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      rw [← Submodule.Quotient.mk_smul (Ideal.span {e}) r z, Algebra.smul_def,
        hs r]
      exact map_mul (Ideal.Quotient.mk (Ideal.span {e})) _ _
  have hQfirst : Ideal.map (RingHom.fst L D) Q' = Ideal.map μ.toRingHom Q := by
    simp only [Q', Ideal.map_map, hfirst]
  have hQprod : Q' = Ideal.prod (Ideal.map μ.toRingHom Q) K := by
    rw [Ideal.ideal_prod_eq Q', hQfirst]
  let q1' : T ⧸ Q ≃+* ((L × D) ⧸ Ideal.prod (Ideal.map μ.toRingHom Q) K) :=
    Ideal.quotientEquiv Q (Ideal.prod (Ideal.map μ.toRingHom Q) K) ψ hQprod.symm
  let p : (L × D) →+* (L ⧸ Ideal.map μ.toRingHom Q) × (D ⧸ K) :=
    (Ideal.Quotient.mk _).prodMap (Ideal.Quotient.mk _)
  have hpker : RingHom.ker p = Ideal.prod (Ideal.map μ.toRingHom Q) K := by
    rw [show p = (Ideal.Quotient.mk (Ideal.map μ.toRingHom Q)).prodMap
        (Ideal.Quotient.mk K) by rfl, RingHom.ker_prodMap, Ideal.mk_ker, Ideal.mk_ker]
  have hpsurj : Function.Surjective p := by
    rintro ⟨x, y⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨(x, y), rfl⟩
  obtain ⟨pRing, hpRing⟩ := exists_ringEquiv_quotient_comp_mk p hpsurj _ hpker
  let qTotalRing : T ⧸ Q ≃+* (L ⧸ Ideal.map μ.toRingHom Q) × (D ⧸ K) :=
    q1'.trans pRing
  have hqTotal_mk (x : T) : qTotalRing (Ideal.Quotient.mk Q x) =
      (Ideal.Quotient.mk (Ideal.map μ.toRingHom Q) (μ x),
        Ideal.Quotient.mk K ((RingHom.snd L D) (ψ x))) := by
    change pRing (Ideal.Quotient.mk (Ideal.prod (Ideal.map μ.toRingHom Q) K)
      (ψ x)) = _
    change (pRing.toRingHom.comp
      (Ideal.Quotient.mk (Ideal.prod (Ideal.map μ.toRingHom Q) K))) (ψ x) = _
    rw [hpRing]
    apply Prod.ext
    · have hx := DFunLike.congr_fun hfirst x
      have hx' : (RingHom.fst L D) (ψ.toRingHom x) = μ.toRingHom x := by
        simpa only [RingHom.comp_apply] using hx
      change Ideal.Quotient.mk (Ideal.map μ.toRingHom Q)
          ((RingHom.fst L D) (ψ.toRingHom x)) = _
      exact congrArg (Ideal.Quotient.mk (Ideal.map μ.toRingHom Q)) hx'
    · rfl
  let qTotalMap : (T ⧸ Q) →ₗ[L] (L ⧸ Ideal.map μ.toRingHom Q) × (D ⧸ K) :=
    { toFun := qTotalRing
      map_add' := map_add qTotalRing
      map_smul' := by
        intro r x
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          have hscalar : qTotalRing (algebraMap L (T ⧸ Q) r) =
              (algebraMap L (L ⧸ Ideal.map μ.toRingHom Q) r,
                algebraMap L (D ⧸ K) r) := by
            have hμr : μ (algebraMap L T r) = r := by simp
            have hψr : ψ (algebraMap L T r) = (r, algebraMap L D r) := by
              change ψA (algebraMap L T r) = (r, algebraMap L D r)
              rw [ψA.commutes r]
              rfl
            rw [← Ideal.Quotient.mk_algebraMap L Q r, hqTotal_mk]
            apply Prod.ext
            · rw [hμr]
              exact (Ideal.Quotient.mk_algebraMap L (Ideal.map μ.toRingHom Q) r).symm
            · rw [hψr]
              exact (Ideal.Quotient.mk_algebraMap L K r).symm
          rw [Algebra.smul_def, map_mul]
          rw [hscalar]
          rw [show Submodule.Quotient.mk x = Ideal.Quotient.mk Q x by rfl,
            hqTotal_mk]
          apply Prod.ext
          · simp only [Prod.fst_mul, Prod.smul_fst, Algebra.smul_def,
              RingHom.id_apply]
          · simp only [Prod.snd_mul, Prod.smul_snd]
            change (algebraMap L (D ⧸ K) r) *
                (Ideal.Quotient.mk K ((RingHom.snd L D) (ψ x))) =
              r • (Submodule.Quotient.mk ((RingHom.snd L D) (ψ x)))
            rw [← Submodule.Quotient.mk_smul K r ((RingHom.snd L D) (ψ x))]
            rw [hsmul, ← Ideal.Quotient.mk_algebraMap L K r, ← map_mul]
            rfl }
  let qTotal : (T ⧸ Q) ≃ₗ[L] (L ⧸ Ideal.map μ.toRingHom Q) × (D ⧸ K) :=
    LinearEquiv.ofBijective qTotalMap ⟨qTotalRing.injective, qTotalRing.surjective⟩
  let J' : Ideal L := fittingIdeal (R := L) (M := D ⧸ K) 0
  refine ⟨J', ?_, ?_⟩
  · have hfit : fittingIdeal (R := L) (M := T ⧸ Q) 0 =
        fittingIdeal (R := L)
          (M := (L ⧸ Ideal.map μ.toRingHom Q) × (D ⧸ K)) 0 :=
      fittingIdeal_eq_of_linearEquiv qTotal 0
    have hprod := (fittingIdeal_basic_properties.{u_1, u_1, u_2, u_1}
      (R := L) (M := L ⧸ Ideal.map μ.toRingHom Q)).2.1 (D ⧸ K) |>.1
    have hquot := (fittingIdeal_basic_properties.{u_1, u_1, u_2, u_1}
      (R := L) (M := L ⧸ Ideal.map μ.toRingHom Q)).2.2.2.2.2.2.2
      (Ideal.map μ.toRingHom Q)
    rw [hquot] at hprod
    simpa [J'] using hfit.trans hprod
  · intro hQ
    have hK : K.FG := (hQ.map ψ.toRingHom).map (RingHom.snd L D)
    have : Module.FinitePresentation L D :=
      finitePresentation_quotient_of_fg (Ideal.span {e}) ⟨{e}, by simp⟩
    exact fittingIdealZero_quotient_fg_of_finitePresentation K hK

/-- **Stacks Project, Tag 0812.** Let `C` be a finite locally free `A`-algebra and let `J` be
an ideal of `C`. If `C` becomes étale over `A` after inverting `h`, then the extension of
the zeroth Fitting ideal of `C ⧸ J` is the product of the extension of `J` with another
ideal. This other ideal can be chosen finitely generated whenever `J` is finitely
generated. -/
@[stacks 0812 "factorization after localization"]
theorem map_fittingIdealZero_quotient_eq_mul_of_etale_away
    (A : Type u) (C : Type v) [CommRing A] [CommRing C] [Algebra A C]
    [Module.Finite A C] [Module.Projective A C] (h : C)
    (het : Algebra.Etale A (Localization.Away h)) (J : Ideal C) :
    ∃ J' : Ideal (Localization.Away h),
      (fittingIdeal (R := A) (M := C ⧸ J) 0).map (algebraMap A (Localization.Away h)) =
          J.map (algebraMap C (Localization.Away h)) * J' ∧
        (J.FG → J'.FG) := by
  classical
  let L := Localization.Away h
  let T := L ⊗[A] C
  let : Algebra L T := Algebra.TensorProduct.leftAlgebra
  let : IsScalarTower A L T := inferInstance
  let : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let : Module.Finite L T := inferInstance
  let : Module.Projective L T :=
    Module.Projective.tensorProduct (R := L) (R₀ := A) (M := L) (N := C)
  let : Module.FinitePresentation L T := Module.finitePresentation_of_projective L T
  let : Algebra.Etale A L := het
  let : IsLocalization.Away h L := inferInstance
  let : Algebra.Etale C (C ⊗[A] L) := Algebra.Etale.baseChange (R := A) (A := L) (B := C)
  let ecomm : C ⊗[A] L ≃ₐ[C] T := AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.comm A C L).toRingEquiv) (by
      intro x
      change (Algebra.TensorProduct.comm A C L) (x ⊗ₜ[A] (1 : L)) =
        (1 : L) ⊗ₜ[A] x
      rw [Algebra.TensorProduct.comm_tmul])
  let : Algebra.Etale C T := Algebra.Etale.of_equiv ecomm
  let hcomm : ∀ x : L, ∀ y : C,
      Commute ((AlgHom.id L L) x) ((IsScalarTower.toAlgHom A C L) y) :=
    fun x y => Commute.all _ _
  let μ : T →ₐ[L] L := Algebra.TensorProduct.lift (AlgHom.id L L)
    (IsScalarTower.toAlgHom A C L) hcomm
  have hcomp : μ.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := A) (A := L) (B := C)).toRingHom =
      algebraMap C L := by
    ext x
    exact DFunLike.congr_fun
      (Algebra.TensorProduct.lift_comp_includeRight
        (f := AlgHom.id L L) (g := IsScalarTower.toAlgHom A C L) (hfg := hcomm)) x
  have hμet : μ.toRingHom.Etale := by
    have hf : (algebraMap C T).Etale :=
      (RingHom.etale_algebraMap (R := C) (S := T)).2 inferInstance
    have hfft : (algebraMap C T).FiniteType :=
      RingHom.FiniteType.of_finitePresentation
        ((RingHom.finitePresentation_algebraMap (A := C) (B := T)).2 inferInstance)
    apply RingHom.Etale.of_comp (f := algebraMap C T) (g := μ.toRingHom)
      (RingHom.Etale.formallyUnramified _ hf) hfft
    rw [show μ.toRingHom.comp (algebraMap C T) = algebraMap C L from hcomp]
    exact (RingHom.etale_algebraMap (R := C) (S := L)).mpr
      (Algebra.Etale.of_isLocalizationAway h)
  let : μ.toRingHom.Etale := hμet
  let : Algebra T L := μ.toRingHom.toAlgebra
  let : Algebra.Etale T L := (RingHom.etale_algebraMap (R := T) (S := L)).mp hμet
  let : Module.Flat T L := inferInstance
  have hsec : μ.comp (Algebra.TensorProduct.includeLeft (R := A) (S := L)
      (A := L) (B := C)) = AlgHom.id L L := by
    simpa only [μ] using
      (Algebra.TensorProduct.lift_comp_includeLeft
        (f := AlgHom.id L L) (g := IsScalarTower.toAlgHom A C L) (hfg := hcomm))
  have hμsurj : Function.Surjective (algebraMap T L) := by
    intro x
    refine ⟨algebraMap L T x, ?_⟩
    change (μ.comp (Algebra.TensorProduct.includeLeft (R := A) (S := L)
      (A := L) (B := C))) x = x
    rw [hsec]
    rfl
  have : Algebra.FinitePresentation T L := inferInstance
  obtain ⟨e, he, hker, _⟩ :=
    Algebra.exists_isIdempotentElem_isLocalizationAway_of_surjective T L hμsurj
  let Q : Ideal T :=
    Ideal.map (Algebra.TensorProduct.includeRight (R := A) (A := L) (B := C)) J
  have hfitBase : fittingIdeal (R := L) (M := T ⧸ Q) 0 =
      (fittingIdeal (R := A) (M := C ⧸ J) 0).map (algebraMap A L) := by
    let eQ : L ⊗[A] (C ⧸ J) ≃ₐ[L] T ⧸ Q :=
      Algebra.TensorProduct.tensorQuotientEquiv (R := A) L C L J
    have hbase := (fittingIdeal_basic_properties.{u, v, v, v}
      (R := A) (M := C ⧸ J)).2.2.1 L 0
    have hlin : (L ⊗[A] (C ⧸ J)) ≃ₗ[L] T ⧸ Q := eQ.toLinearEquiv
    calc
      fittingIdeal (R := L) (M := T ⧸ Q) 0 =
          fittingIdeal (R := L) (M := L ⊗[A] (C ⧸ J)) 0 :=
        (fittingIdeal_eq_of_linearEquiv hlin 0).symm
      _ = (fittingIdeal (R := A) (M := C ⧸ J) 0).map (algebraMap A L) := hbase
  obtain ⟨J', hsplit, hfg⟩ :=
    fittingIdeal_split_quotient μ hμsurj e he hker Q
  have hmap : Ideal.map μ.toRingHom Q = J.map (algebraMap C L) := by
    change (J.map (Algebra.TensorProduct.includeRight
      (R := A) (A := L) (B := C)).toRingHom).map μ.toRingHom =
      J.map (algebraMap C L)
    rw [Ideal.map_map, hcomp]
  refine ⟨J', ?_, ?_⟩
  · rw [← hfitBase, hsplit, hmap]
  · intro hJ
    apply hfg
    exact hJ.map _

/-- An element of the annihilator of a finite module lies in the radical of the module's
zeroth Fitting ideal. -/
private lemma mem_radical_fittingIdeal_zero_of_mem_annihilator
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (x : R) (hx : x ∈ Module.annihilator R M) :
    x ∈ (fittingIdeal (R := R) (M := M) 0).radical := by
  have hs := (fittingIdeal_basic_properties.{u, v, v, u}
    (R := R) (M := M)).2.2.2.2.2.2.1
  rw [Module.support_eq_zeroLocus] at hs
  exact ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hs.le) hx

/-- Every finitely generated ideal of a localization is the extension of a finitely generated
ideal of the base ring. -/
private lemma exists_fg_ideal_map_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (I : Ideal S) (hI : I.FG) :
    ∃ K : Ideal R, K.FG ∧ K.map (algebraMap R S) = I := by
  classical
  obtain ⟨t, htfin, ht⟩ := Submodule.fg_def.mp hI
  choose num den hnum using fun x : S => IsLocalization.exists_mk'_eq M x
  let K : Ideal R := Ideal.span (num '' t)
  refine ⟨K, Submodule.fg_span (htfin.image num), ?_⟩
  rw [Ideal.map_span, ← ht]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    rw [← IsLocalization.mk'_spec S (num z) (den z), hnum z]
    exact (Ideal.span t).mul_mem_right _ (Ideal.subset_span hz)
  · rw [Ideal.span_le]
    intro x hx
    have hnum_mem : algebraMap R S (num x) ∈
        Ideal.span ((algebraMap R S) '' (num '' t)) :=
      Ideal.subset_span ⟨num x, ⟨x, hx, rfl⟩, rfl⟩
    rw [← IsLocalization.mk'_spec S (num x) (den x), hnum x] at hnum_mem
    exact (Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S (den x))).mp
      (by simpa [mul_comm] using hnum_mem)

/-- **Stacks Project, Tag 0813.** Let `A → B` be étale, let `a ∈ A`, and let `J` be a
finitely generated ideal of `B` with `V(J) ⊆ V(aB)`. At every prime `q` of `B`,
after localizing at some `g ∉ q`, the extension of a finitely generated ideal
`I` of `A`, with `V(I) ⊆ V(a)`, is the product of the extension of `J` and a
finitely generated ideal. -/
@[stacks 0813]
theorem exists_ideal_map_eq_mul_after_localization
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Etale A B] (a : A) (J : Ideal B) (hJ : J.FG)
    (hV : algebraMap A B a ∈ J.radical) (q : Ideal B) [q.IsPrime] :
    ∃ I : Ideal A, I.FG ∧ a ∈ I.radical ∧
      ∃ g : B, g ∉ q ∧
        ∃ J' : Ideal (Localization.Away g), J'.FG ∧
          Ideal.map ((algebraMap B (Localization.Away g)).comp (algebraMap A B)) I =
            Ideal.map (algebraMap B (Localization.Away g)) J * J' := by
  classical
  obtain ⟨g, hgq, hstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := A) (S := B) q
  let _ : Algebra.IsStandardEtale A (Localization.Away g) := hstd
  let P : StandardEtalePresentation A (Localization.Away g) :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let C := AdjoinRoot P.f
  let h : C := AdjoinRoot.mk P.f P.g
  let e : Localization.Away g ≃ₐ[A] Localization.Away h :=
    P.equivRing.trans P.P.equivAwayAdjoinRoot
  let _ : Module.Free A C := P.monic_f.free_adjoinRoot
  let _ : Module.Finite A C := P.monic_f.finite_adjoinRoot
  let _ : Algebra.Etale A (Localization.Away h) := Algebra.Etale.of_equiv e
  let JL : Ideal (Localization.Away g) := J.map (algebraMap B (Localization.Away g))
  let JC : Ideal (Localization.Away h) := JL.map e.toRingHom
  have hJC : JC.FG := (hJ.map _).map _
  obtain ⟨K₀, hK₀, hK₀map⟩ :=
    exists_fg_ideal_map_eq (Submonoid.powers h) JC hJC
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hV
  let K : Ideal C := K₀ ⊔ Ideal.span {algebraMap A C (a ^ n)}
  have hpowJC : algebraMap A (Localization.Away h) (a ^ n) ∈ JC := by
    rw [← e.commutes]
    change e (algebraMap B (Localization.Away g) (algebraMap A B (a ^ n))) ∈ JC
    apply Ideal.mem_map_of_mem
    exact Ideal.mem_map_of_mem _ (by simpa using hn)
  have hKmap : K.map (algebraMap C (Localization.Away h)) = JC := by
    rw [Ideal.map_sup, hK₀map, sup_eq_left, Ideal.map_span, Ideal.span_le]
    rintro x ⟨y, hy, rfl⟩
    rcases hy with rfl
    simpa [IsScalarTower.algebraMap_apply A C (Localization.Away h)] using hpowJC
  have hK : K.FG := Submodule.FG.sup hK₀ (Submodule.fg_span (Set.finite_singleton _))
  let I : Ideal A := fittingIdeal (R := A) (M := C ⧸ K) 0
  have haann : a ^ n ∈ Module.annihilator A (C ⧸ K) := by
    apply Module.mem_annihilator.mpr
    intro z
    induction z using Quotient.inductionOn with
    | _ z =>
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      simpa [Algebra.smul_def] using K.mul_mem_right z
        (show algebraMap A C (a ^ n) ∈ K from
          le_sup_right (a := K₀) (b := Ideal.span {algebraMap A C (a ^ n)})
            (Ideal.subset_span (Set.mem_singleton _)))
  have haI : a ∈ I.radical := by
    obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp
      (mem_radical_fittingIdeal_zero_of_mem_annihilator (a ^ n) haann)
    rw [Ideal.mem_radical_iff]
    exact ⟨n * m, by simpa [pow_mul] using hm⟩
  obtain ⟨J', hfac, hJ'⟩ :=
    map_fittingIdealZero_quotient_eq_mul_of_etale_away A C h
      (show Algebra.Etale A (Localization.Away h) from inferInstance) K
  refine ⟨I, fittingIdealZero_quotient_fg A C K hK, haI, g, hgq,
    J'.map e.symm.toRingHom, hJ' hK |>.map _, ?_⟩
  rw [hKmap] at hfac
  have heq := congrArg (Ideal.map e.symm.toRingHom) hfac
  have hbase : e.symm.toRingHom.comp (algebraMap A (Localization.Away h)) =
      (algebraMap B (Localization.Away g)).comp (algebraMap A B) := by
    ext x
    change e.symm (algebraMap A (Localization.Away h) x) = _
    rw [e.symm.commutes]
    exact IsScalarTower.algebraMap_apply A B (Localization.Away g) x
  have hcancelB : e.symm.toRingHom.comp
      (e.toRingHom.comp (algebraMap B (Localization.Away g))) =
      algebraMap B (Localization.Away g) := by
    ext x
    simp
  simp only [JC, JL, Ideal.map_mul, Ideal.map_map] at heq
  rw [hbase, hcancelB] at heq
  simpa [I] using heq
