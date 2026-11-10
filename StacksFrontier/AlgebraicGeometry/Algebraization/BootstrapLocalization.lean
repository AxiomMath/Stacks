module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.BootstrapSituation
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.RingTheory.AdicCompletion.EvalFactorPow
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.ChangeOfRings

/-!
# Localization of a bootstrap situation

A bootstrap situation localizes: for a multiplicative subset `S` of the base ring `A`, the
localization `S⁻¹A`, the extended ideal, the localized module and the preimage of the locus
`T` again satisfy all four bootstrap assumptions, with the same bounds `s` and `d`.

Each assumption transfers for its own reason. A dualizing complex localizes (Tag 0A7G).
Cohomological dimension does not increase under a ring map (Tag 0DXA). The two depth
assumptions reduce to the original ones because a prime of `S⁻¹A` and its contraction have
the same local ring and the same localized module, and because the adic completion of a
localization of `S⁻¹A` is canonically the adic completion of the corresponding localization
of `A`.

## Main results

* `Stacks.Algebraization.BootstrapSituation.localize` — the localized bootstrap situation.
* `Stacks.Algebraization.subset_adicLocus_localization`,
  `Stacks.Algebraization.stableUnderSpecialization_localization`,
  `Stacks.Algebraization.dualizing_localization`,
  `Stacks.Algebraization.cohomologicalDimension_le_localization`,
  `Stacks.Algebraization.depth_or_depth_add_dimension_localization`,
  `Stacks.Algebraization.completedLocalDepth_localization` — the four assumptions, and the two
  conditions on the locus, after localization.

## Implementation notes

The comparison of the two completions is a ring isomorphism together with a compatible
semilinear equivalence of modules over it; `AdicCompletionRingBridge` bundles that pair, and
the depth computations are transported along it. Depth and dimension are compared in the
extended integers, as in the situation itself.

## References

* [Stacks Project, Tag 0EFV](https://stacks.math.columbia.edu/tag/0EFV)
-/

@[expose] public section

open CategoryTheory IsLocalRing

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Stacks.Algebraization

/-- A ring isomorphism of adic completions induced by a ring isomorphism of the bases, together
with its compatibility with the two structure maps. -/
private structure AdicCompletionRingBridge {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S) where
  equiv : AdicCompletion I R ≃+* AdicCompletion J S
  map_base : ∀ r : R,
    equiv (algebraMap R (AdicCompletion I R) r) =
      algebraMap S (AdicCompletion J S) (e r)

/-- The adic completion of a ring transported along a ring isomorphism identifying the two
ideals. -/
private noncomputable def adicCompletion_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    (hI : J = I.map e.toRingHom) :
    AdicCompletionRingBridge I J e := by
  let qn (n : ℕ) : R ⧸ I ^ n ≃+* S ⧸ J ^ n := by
    apply Ideal.quotientEquiv (I ^ n) (J ^ n) e
    calc
      J ^ n = (I.map e.toRingHom) ^ n := by rw [hI]
      _ = (I ^ n).map e.toRingHom := by rw [← Ideal.map_pow]
  let f (n : ℕ) : AdicCompletion I R →+* S ⧸ J ^ n :=
    (qn n).toRingHom.comp (AdicCompletion.evalₐ I n).toRingHom
  have hf : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow J hle).comp (f n) = f m := by
    intro m n hle
    have hcomm : (Ideal.Quotient.factorPow J hle).comp (qn n).toRingHom =
        (qn m).toRingHom.comp (Ideal.Quotient.factorPow I hle) := by
      apply RingHom.ext
      intro x
      induction x using Quotient.inductionOn' with
      | h a => rfl
    ext x
    dsimp only [f]
    change ((Ideal.Quotient.factorPow J hle).comp (qn n).toRingHom)
        (AdicCompletion.evalₐ I n x) =
      (qn m).toRingHom (AdicCompletion.evalₐ I m x)
    rw [hcomm]
    exact congrArg (qn m) (AdicCompletion.factorPow_evalₐ I hle x)
  let c : AdicCompletion I R →+* AdicCompletion J S :=
    AdicCompletion.liftRingHom J f hf
  let qn' (n : ℕ) : S ⧸ J ^ n ≃+* R ⧸ I ^ n := (qn n).symm
  let g (n : ℕ) : AdicCompletion J S →+* R ⧸ I ^ n :=
    (qn' n).toRingHom.comp (AdicCompletion.evalₐ J n).toRingHom
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow I hle).comp (g n) = g m := by
    intro m n hle
    have hcomm : (Ideal.Quotient.factorPow I hle).comp (qn' n).toRingHom =
        (qn' m).toRingHom.comp (Ideal.Quotient.factorPow J hle) := by
      apply RingHom.ext
      intro x
      induction x using Quotient.inductionOn' with
      | h a => rfl
    ext x
    dsimp only [g]
    change ((Ideal.Quotient.factorPow I hle).comp (qn' n).toRingHom)
        (AdicCompletion.evalₐ J n x) =
      (qn' m).toRingHom (AdicCompletion.evalₐ J m x)
    rw [hcomm]
    exact congrArg (qn' m) (AdicCompletion.factorPow_evalₐ J hle x)
  let d : AdicCompletion J S →+* AdicCompletion I R :=
    AdicCompletion.liftRingHom I g hg
  have hcd : d.comp c = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n
      (AdicCompletion.liftRingHom I g hg (AdicCompletion.liftRingHom J f hf x)) = _
    rw [AdicCompletion.evalₐ_liftRingHom]
    change (g n) (AdicCompletion.liftRingHom J f hf x) = _
    change (qn' n).toRingHom
      (AdicCompletion.evalₐ J n (AdicCompletion.liftRingHom J f hf x)) = _
    rw [AdicCompletion.evalₐ_liftRingHom]
    change qn' n (qn n (AdicCompletion.evalₐ I n x)) = _
    change (qn n).symm (qn n (AdicCompletion.evalₐ I n x)) = _
    simp only [RingHom.id_apply]
    exact (qn n).symm_apply_apply _
  have hdc : c.comp d = RingHom.id _ := by
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ J n
      (AdicCompletion.liftRingHom J f hf (AdicCompletion.liftRingHom I g hg x)) = _
    rw [AdicCompletion.evalₐ_liftRingHom]
    change (f n) (AdicCompletion.liftRingHom I g hg x) = _
    change (qn n).toRingHom
      (AdicCompletion.evalₐ I n (AdicCompletion.liftRingHom I g hg x)) = _
    rw [AdicCompletion.evalₐ_liftRingHom]
    change qn n (qn' n (AdicCompletion.evalₐ J n x)) = _
    change (qn n) ((qn n).symm (AdicCompletion.evalₐ J n x)) = _
    simp only [RingHom.id_apply]
    exact (qn n).apply_symm_apply _
  have hc : Function.Bijective c := by
    constructor
    · intro x y hxy
      have hxy' := congrArg d hxy
      have hx := RingHom.congr_fun hcd x
      have hy := RingHom.congr_fun hcd y
      simpa [RingHom.comp_apply] using hx.symm.trans (hxy'.trans hy)
    · intro y
      refine ⟨d y, ?_⟩
      simpa [RingHom.comp_apply] using RingHom.congr_fun hdc y
  let E : AdicCompletion I R ≃+* AdicCompletion J S := RingEquiv.ofBijective c hc
  refine ⟨E, ?_⟩
  intro r
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ J n (c (AdicCompletion.of I R r)) = _
  dsimp only [c]
  rw [AdicCompletion.evalₐ_liftRingHom]
  change qn n (Ideal.Quotient.mk (I ^ n) r) =
    AdicCompletion.evalₐ J n (AdicCompletion.of J S (e r))
  rw [AdicCompletion.evalₐ_of]
  exact Ideal.quotientEquiv_mk _ _ e (by
    calc
      J ^ n = (I.map e.toRingHom) ^ n := by rw [hI]
      _ = (I ^ n).map e.toRingHom := by rw [← Ideal.map_pow]) r

/-- For a finite module over a Noetherian ring, adic completion is extension of scalars to the
completed ring. -/
private noncomputable def adicCompletionTensorEquiv
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    TensorProduct R (AdicCompletion I R) M ≃ₗ[AdicCompletion I R] AdicCompletion I M := by
  have : Small.{u} M := Module.Finite.small R M
  let e := Shrink.linearEquiv R M
  have hbij : Function.Bijective (AdicCompletion.ofTensorProduct I M) := by
    apply (Function.Bijective.of_comp_iff
      (AdicCompletion.ofTensorProduct I M)
      (e.baseChange R (AdicCompletion I R) (Shrink.{u} M) M).bijective).mp
    change Function.Bijective
      (AdicCompletion.ofTensorProduct I M ∘ₗ
        e.toLinearMap.baseChange (AdicCompletion I R))
    rw [LinearMap.baseChange, ← AdicCompletion.ofTensorProduct_naturality]
    exact (AdicCompletion.congr I e).bijective.comp
      (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I (Shrink.{u} M)).bijective
  exact LinearEquiv.ofBijective (AdicCompletion.ofTensorProduct I M) hbij

/-- A semilinear equivalence of modules over a ring isomorphism `e` induces one on base changes,
along an isomorphism of the base algebras compatible with `e`. -/
private noncomputable def tensorProduct_semilinearEquiv
    {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    [Algebra R T] [Algebra S U] (e : R ≃+* S) (eT : T ≃+* U)
    [RingHomInvPair e.toRingHom e.symm.toRingHom]
    [RingHomInvPair e.symm.toRingHom e.toRingHom]
    [RingHomInvPair eT.toRingHom eT.symm.toRingHom]
    [RingHomInvPair eT.symm.toRingHom eT.toRingHom]
    (hsmul : ∀ (r : R) (a : T), eT (r • a) = e r • eT a)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M ≃ₛₗ[e.toRingHom] N) :
    TensorProduct R T M ≃ₛₗ[eT.toRingHom] TensorProduct S U N := by
  let eLs : T ≃ₛₗ[e.toRingHom] U := { eT.toAddEquiv with map_smul' := hsmul }
  let t₀ := TensorProduct.congr eLs f
  have key : ∀ (r : T) (z : TensorProduct R T M), t₀ (r • z) = eT r • t₀ z := by
    intro r z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']
    | tmul a m =>
        simp only [TensorProduct.smul_tmul', t₀]
        change eT (r * a) ⊗ₜ[S] f m = (eT r * eT a) ⊗ₜ[S] f m
        rw [map_mul]
  exact { t₀.toAddEquiv with map_smul' := key }

/-- A semilinear equivalence of finite modules induces one of their adic completions. -/
private noncomputable def adicCompletion_moduleSemilinearEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    [RingHomInvPair e.toRingHom e.symm.toRingHom]
    [RingHomInvPair e.symm.toRingHom e.toRingHom]
    (hI : J = I.map e.toRingHom)
    [RingHomInvPair (adicCompletion_ringEquiv I J e hI).equiv.toRingHom
      (adicCompletion_ringEquiv I J e hI).equiv.symm.toRingHom]
    [RingHomInvPair (adicCompletion_ringEquiv I J e hI).equiv.symm.toRingHom
      (adicCompletion_ringEquiv I J e hI).equiv.toRingHom]
    {M : Type*} {N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module S N] [Module.Finite S N]
    (f : M ≃ₛₗ[e.toRingHom] N) :
    AdicCompletion I M ≃ₛₗ[
      (adicCompletion_ringEquiv I J e hI).equiv.toRingHom]
      AdicCompletion J N :=
  let b := adicCompletion_ringEquiv I J e hI
  let t := tensorProduct_semilinearEquiv e b.equiv (fun r a => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, b.map_base]) f
  (adicCompletionTensorEquiv I (M := M)).symm.trans
    (t.trans (adicCompletionTensorEquiv J (M := N)))

/-- The localization of `M` at the contraction of a prime of `S⁻¹A` is semilinearly isomorphic to
the localization of `S⁻¹M` at that prime. -/
private noncomputable def localizedModule_localizationLocalizationEquiv
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (S : Submonoid A) (q : Ideal (Localization S)) [q.IsPrime]
    [RingHomInvPair
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := S) q).toRingEquiv.toRingHom
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := S) q).toRingEquiv.symm.toRingHom]
    [RingHomInvPair
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := S) q).toRingEquiv.symm.toRingHom
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := S) q).toRingEquiv.toRingHom] :
    LocalizedModule ((q.comap (algebraMap A (Localization S))).primeCompl) M ≃ₛₗ[
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (M := S) q).toRingEquiv.toRingHom]
      LocalizedModule q.primeCompl (LocalizedModule S M) := by
  classical
  let p := q.comap (algebraMap A (Localization S))
  let L0 := Localization.AtPrime p
  let L1 := Localization.AtPrime q
  let M0 := LocalizedModule p.primeCompl M
  let MS := LocalizedModule S M
  let M1 := LocalizedModule q.primeCompl MS
  let e : L0 ≃ₐ[A] L1 :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := S) q
  letI : Algebra L0 L1 := RingHom.toAlgebra e.toRingEquiv.toRingHom
  letI : Module L1 M0 := Module.compHom M0 e.toRingEquiv.symm.toRingHom
  letI : IsScalarTower L0 L1 M0 := IsScalarTower.of_algebraMap_smul fun x m => by
    have hx : e.toRingEquiv.symm (algebraMap L0 L1 x) = x := by
      change e.toRingEquiv.symm (e.toRingEquiv x) = x
      exact e.toRingEquiv.symm_apply_apply x
    exact congrArg (fun z => z • m) hx
  letI : IsScalarTower A L0 L1 := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (e.commutes x).symm)
  letI : IsScalarTower A L1 M0 := IsScalarTower.of_algebraMap_smul fun x m => by
    change e.toRingEquiv.symm (algebraMap A L1 x) • m = x • m
    have hcomm : e.toRingEquiv (algebraMap A L0 x) = algebraMap A L1 x := e.commutes x
    calc
      e.toRingEquiv.symm (algebraMap A L1 x) • m = (algebraMap A L0 x) • m := by
        rw [← hcomm, e.toRingEquiv.symm_apply_apply]
      _ = x • m := IsScalarTower.algebraMap_smul L0 x m
  let f₁ : M →ₗ[A] MS := LocalizedModule.mkLinearMap S M
  let f₂ : MS →ₗ[Localization S] M1 := LocalizedModule.mkLinearMap q.primeCompl MS
  let f : M →ₗ[A] M1 := (f₂.restrictScalars A).comp f₁
  have hstandard : IsBaseChange L1 (LocalizedModule.mkLinearMap p.primeCompl M) :=
    IsLocalizedModule.isBaseChange p.primeCompl L1 _
  have hfirst : IsBaseChange (Localization S) f₁ := LocalizedModule.isBaseChange S M
  have hsecond : IsBaseChange L1 f₂ := IsLocalizedModule.isBaseChange q.primeCompl L1 f₂
  have hcomp : IsBaseChange L1 f := by
    dsimp [f]
    exact hfirst.comp hsecond
  let eM : M0 ≃ₗ[L1] M1 := hstandard.equiv.symm.trans hcomp.equiv
  haveI : RingHomInvPair e.toRingEquiv.toRingHom e.toRingEquiv.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e.toRingEquiv
  haveI : RingHomInvPair e.toRingEquiv.symm.toRingHom e.toRingEquiv.toRingHom :=
    RingHomInvPair.symm e.toRingEquiv.toRingHom e.toRingEquiv.symm.toRingHom
  exact { eM.toAddEquiv with
    map_smul' := fun r m => by
      change eM (r • m) = e.toRingEquiv r • eM m
      have hs : (algebraMap L0 L1 r) • m = r • m :=
        IsScalarTower.algebraMap_smul (A := L1) r m
      calc
        eM (r • m) = eM ((algebraMap L0 L1 r) • m) := by rw [hs]
        _ = (algebraMap L0 L1 r) • eM m := eM.map_smul _ _
        _ = e.toRingEquiv r • eM m := rfl }

/-- Extending an ideal of `A` to the local ring at the contraction of a prime `q` of `S⁻¹A` and
transporting it along the canonical isomorphism agrees with extending it to the local ring at `q`
through `S⁻¹A`. -/
private theorem map_map_localizationLocalizationAtPrimeIso
    {A : Type u} [CommRing A] (S : Submonoid A) (q : Ideal (Localization S)) [q.IsPrime]
    (I : Ideal A) :
    (I.map (algebraMap A (Localization.AtPrime (q.comap (algebraMap A (Localization S)))))).map
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (M := S) q).toRingEquiv.toRingHom =
      (I.map (algebraMap A (Localization S))).map
        (algebraMap (Localization S) (Localization.AtPrime q)) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  exact ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (M := S) q).commutes x).trans (IsScalarTower.algebraMap_apply A (Localization S) _ x)

/-- The relative dimension between two primes of `S⁻¹A` agrees with the relative dimension
between their contractions. -/
private theorem ringKrullDim_quotient_localizationLocalization
    {A : Type u} [CommRing A] (S : Submonoid A)
    (p q : PrimeSpectrum (Localization S)) (_hpq : p.asIdeal ≤ q.asIdeal) :
    ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
        p.asIdeal.map (algebraMap (Localization S) (Localization.AtPrime q.asIdeal))) =
      ringKrullDim ((Localization.AtPrime (q.asIdeal.comap (algebraMap A (Localization S)))) ⧸
        (p.asIdeal.comap (algebraMap A (Localization S))).map
          (algebraMap A
            (Localization.AtPrime (q.asIdeal.comap (algebraMap A (Localization S)))))) := by
  let p₀ := p.asIdeal.comap (algebraMap A (Localization S))
  let q₀ := q.asIdeal.comap (algebraMap A (Localization S))
  let L₀ := Localization.AtPrime q₀
  let L₁ := Localization.AtPrime q.asIdeal
  let e : L₀ ≃ₐ[A] L₁ :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := S) q.asIdeal
  have hpmap : p₀.map (algebraMap A (Localization S)) = p.asIdeal :=
    IsLocalization.map_under S (Localization S) p.asIdeal
  have hmap := map_map_localizationLocalizationAtPrimeIso S q.asIdeal p₀
  rw [hpmap] at hmap
  let equot := Ideal.quotientEquiv _ _ e.toRingEquiv hmap.symm
  exact (ringKrullDim_eq_of_ringEquiv equot).symm

/-- The semilinear comparison of the two localized modules used in the depth computation. -/
private noncomputable def localizedModuleSemilinearEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (e : R ≃+* S)
    [I.IsPrime] [J.IsPrime]
    (_hI : J = I.map e.toRingHom)
    (hS : Submonoid.map e.toMonoidHom I.primeCompl = J.primeCompl)
    [RingHomInvPair e.toRingHom e.symm.toRingHom]
    [RingHomInvPair e.symm.toRingHom e.toRingHom]
    [RingHomInvPair
      (IsLocalization.ringEquivOfRingEquiv (Localization I.primeCompl)
        (Localization J.primeCompl) e hS).toRingHom
      (IsLocalization.ringEquivOfRingEquiv (Localization I.primeCompl)
        (Localization J.primeCompl) e hS).symm.toRingHom]
    [RingHomInvPair
      (IsLocalization.ringEquivOfRingEquiv (Localization I.primeCompl)
        (Localization J.primeCompl) e hS).symm.toRingHom
      (IsLocalization.ringEquivOfRingEquiv (Localization I.primeCompl)
        (Localization J.primeCompl) e hS).toRingHom]
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N]
    (f : M ≃ₛₗ[e.toRingHom] N) :
    LocalizedModule I.primeCompl M ≃ₛₗ[
      (IsLocalization.ringEquivOfRingEquiv (Localization I.primeCompl)
        (Localization J.primeCompl) e hS).toRingHom]
      LocalizedModule J.primeCompl N := by
  letI : Algebra R S := RingHom.toAlgebra e.toRingHom
  let h : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)
  let hL : Localization I.primeCompl ≃ₐ[R] Localization J.primeCompl :=
    IsLocalization.algEquivOfAlgEquiv (Localization I.primeCompl)
      (Localization J.primeCompl) h hS
  let eL := hL.toRingEquiv
  letI : RingHomInvPair eL.toRingHom eL.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv eL
  letI : RingHomInvPair eL.symm.toRingHom eL.toRingHom :=
    RingHomInvPair.symm eL.toRingHom eL.symm.toRingHom
  let t := tensorProduct_semilinearEquiv e eL (fun r x => by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    exact congrArg (· * eL x) ((hL.commutes r).trans
      (IsScalarTower.algebraMap_apply R S (Localization J.primeCompl) r).symm)) f
  exact (LocalizedModule.equivTensorProduct I.primeCompl M).trans
    (t.trans (LocalizedModule.equivTensorProduct J.primeCompl N).symm)

/-- Depth is invariant under a semilinear equivalence of modules over a ring isomorphism carrying
one ideal to the other. -/
private theorem depth_eq_of_ringModuleSemilinearEquiv
    {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module S N]
    [RingHomInvPair e.toRingHom e.symm.toRingHom]
    [RingHomInvPair e.symm.toRingHom e.toRingHom]
    (f : M ≃ₛₗ[e.toRingHom] N) (hI : J = I.map e.toRingHom) :
    Module.depth R I M = Module.depth S J N := by
  let : Algebra R S := RingHom.toAlgebra e.toRingHom
  let : Module R N := Module.compHom N e.toRingHom
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r n => rfl
  let f' : M ≃ₗ[R] N := {
    toFun := f
    invFun := f.symm
    left_inv := f.left_inv
    right_inv := f.right_inv
    map_add' := f.map_add
    map_smul' := fun r m => f.map_smulₛₗ r m }
  calc
    Module.depth R I M = Module.depth R I N := Module.depth_eq_depth_of_linearEquiv I f'
    _ = Module.depth S J N := by
      rw [Module.depth_eq_depth_map_algebraMap e.surjective I N]
      change Module.depth S (I.map e.toRingHom) N = Module.depth S J N
      rw [hI]

/-- Localizing at a prime of `S⁻¹A` and localizing at its contraction give modules of the same
depth. -/
private theorem depth_localizedModule_localizationLocalization
    {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
    (S : Submonoid A) (q : Ideal (Localization S)) [q.IsPrime] :
    Module.depth (Localization.AtPrime (q.comap (algebraMap A (Localization S))))
        (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A (Localization S)))))
        (LocalizedModule (q.comap (algebraMap A (Localization S))).primeCompl M) =
      Module.depth (Localization.AtPrime q) (maximalIdeal (Localization.AtPrime q))
        (LocalizedModule q.primeCompl (LocalizedModule S M)) := by
  classical
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := S) q
  let : RingHomInvPair e.toRingEquiv.toRingHom e.toRingEquiv.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e.toRingEquiv
  let : RingHomInvPair e.toRingEquiv.symm.toRingHom e.toRingEquiv.toRingHom :=
    RingHomInvPair.symm e.toRingEquiv.toRingHom e.toRingEquiv.symm.toRingHom
  exact depth_eq_of_ringModuleSemilinearEquiv e.toRingEquiv _ _
    (localizedModule_localizationLocalizationEquiv (M := M) S q)
    (IsLocalRing.map_ringEquiv_maximalIdeal e.toRingEquiv).symm

/-- The locus of the localized situation: the preimage of `T` under the map of spectra. -/
public abbrev locus (X : BootstrapSituation.{u, v, w})
    (S : Submonoid X.A) : Set (PrimeSpectrum (Localization S)) :=
  (PrimeSpectrum.comap (algebraMap X.A (Localization S))) ⁻¹' X.T

/-- The localized locus is contained in the adic locus of the extended ideal. -/
@[stacks 0EFV "localization"]
public theorem subset_adicLocus_localization
    (X : BootstrapSituation.{u, v, w}) (S : Submonoid X.A) :
    locus X S ⊆ PrimeSpectrum.zeroLocus
      ((X.I.map (algebraMap X.A (Localization S))) : Set (Localization S)) :=
  fun _ hp => Ideal.map_le_iff_le_comap.2 (X.subset_adicLocus hp)

/-- The localized locus is stable under specialization. -/
@[stacks 0EFV "localization"]
public theorem stableUnderSpecialization_localization
    (X : BootstrapSituation.{u, v, w}) (S : Submonoid X.A) :
  StableUnderSpecialization (locus X S) :=
  X.stableUnderSpecialization.preimage (PrimeSpectrum.continuous_comap _)

/-- Assumption (1) localizes: a localization of a ring with a dualizing complex has one. -/
@[stacks 0EFV "localization"]
public theorem dualizing_localization
    (X : BootstrapSituation.{u, v, w}) (S : Submonoid X.A) :
    ∃ K : DerivedCategory (ModuleCat.{max u w} (Localization S)),
      Dualizing.IsDualizingComplex K := by
  obtain ⟨K, hK⟩ := X.dualizing
  exact ⟨_, Dualizing.isDualizingComplex_localization (B := Localization S) S K hK⟩

/-- Assumption (3) localizes: cohomological dimension does not increase. -/
@[stacks 0EFV "localization"]
public theorem cohomologicalDimension_le_localization
    (X : BootstrapSituation.{u, v, w}) (S : Submonoid X.A) :
    Stacks.LocalCohomology.cohomologicalDimension (Localization S)
      (X.I.map (algebraMap X.A (Localization S)))
      (Ideal.fg_of_isNoetherianRing _) ≤ X.d :=
  (Stacks.LocalCohomology.cohomologicalDimension_map_le
    (algebraMap X.A (Localization S)) X.I
    (Ideal.fg_of_isNoetherianRing X.I)).trans X.cohomologicalDimension_le

/-- Assumption (4) localizes: the chain-of-primes depth estimate holds for the localized data. -/
@[stacks 0EFV "localization"]
public theorem depth_or_depth_add_dimension_localization
    (X : BootstrapSituation.{u, v, w}) (S : Submonoid X.A) :
    ∀ p r q : PrimeSpectrum (Localization S),
      p.asIdeal ≤ r.asIdeal → r.asIdeal ≤ q.asIdeal →
      p ∉ PrimeSpectrum.zeroLocus
        ((X.I.map (algebraMap X.A (Localization S))) : Set (Localization S)) →
      r ∈ PrimeSpectrum.zeroLocus
        ((X.I.map (algebraMap X.A (Localization S))) : Set (Localization S)) →
      r ∉ locus X S → q ∈ locus X S →
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl (LocalizedModule S X.M))) ≥
          (X.s : EInt)) ∨
      (enatToEInt
          (Module.depth (Localization.AtPrime p.asIdeal)
            (maximalIdeal (Localization.AtPrime p.asIdeal))
            (LocalizedModule p.asIdeal.primeCompl (LocalizedModule S X.M))) +
        krullDimToEInt
          (ringKrullDim ((Localization.AtPrime q.asIdeal) ⧸
            p.asIdeal.map (algebraMap (Localization S)
              (Localization.AtPrime q.asIdeal)))) >
        ((X.d + X.s : ℤ) : EInt)) := by
  intro p r q hpr hrq hpzero hrzero hrnot hq
  let f : X.A →+* Localization S := algebraMap X.A (Localization S)
  let p₀ : PrimeSpectrum X.A := PrimeSpectrum.comap f p
  let r₀ : PrimeSpectrum X.A := PrimeSpectrum.comap f r
  let q₀ : PrimeSpectrum X.A := PrimeSpectrum.comap f q
  have hpzero₀ : p₀ ∉ PrimeSpectrum.zeroLocus (X.I : Set X.A) :=
    fun h => hpzero (Ideal.map_le_iff_le_comap.2 h)
  have hrzero₀ : r₀ ∈ PrimeSpectrum.zeroLocus (X.I : Set X.A) :=
    Ideal.map_le_iff_le_comap.1 hrzero
  have h := X.depth_or_depth_add_dimension p₀ r₀ q₀ (Ideal.comap_mono hpr)
    (Ideal.comap_mono hrq) hpzero₀ hrzero₀ hrnot hq
  have hdepth := depth_localizedModule_localizationLocalization
    (A := X.A) (M := X.M) S p.asIdeal
  have hdim := ringKrullDim_quotient_localizationLocalization
    (A := X.A) S p q (hpr.trans hrq)
  rw [← hdepth, hdim]
  exact h

/-- Assumption (6) localizes: the strict depth bound on completed localizations persists. -/
@[stacks 0EFV "localization"]
public theorem completedLocalDepth_localization
    (X : BootstrapSituation.{u, v, w}) (S : Submonoid X.A) :
    ∀ q : PrimeSpectrum (Localization S), q ∈ locus X S →
      let Aq := Localization.AtPrime q.asIdeal
      let Iq := (X.I.map (algebraMap X.A (Localization S))).map
        (algebraMap (Localization S) Aq)
      let Mq := LocalizedModule q.asIdeal.primeCompl (LocalizedModule S X.M)
      let A' := AdicCompletion Iq Aq
      let I' := Iq.map (algebraMap Aq A')
      let m' := (maximalIdeal Aq).map (algebraMap Aq A')
      ∀ p' : PrimeSpectrum A',
        ¬ I' ≤ p'.asIdeal →
        {r' : Ideal A' | r'.IsPrime ∧ p'.asIdeal ≤ r' ∧ I' ≤ r'} = {m'} →
      enatToEInt
          (Module.depth (Localization.AtPrime p'.asIdeal)
            (maximalIdeal (Localization.AtPrime p'.asIdeal))
            (LocalizedModule p'.asIdeal.primeCompl (AdicCompletion Iq Mq))) >
          (X.s : EInt) :=
  by
    classical
    intro q hq
    dsimp only
    intro p' hpnot huniq
    let f : X.A →+* Localization S := algebraMap X.A (Localization S)
    let q₀ : PrimeSpectrum X.A := PrimeSpectrum.comap f q
    let p₀ : Ideal X.A := q₀.asIdeal
    let : p₀.IsPrime := q₀.isPrime
    change q₀ ∈ X.T at hq
    let R₀ := Localization.AtPrime q₀.asIdeal
    let R₁ := Localization.AtPrime q.asIdeal
    let e : R₀ ≃ₐ[X.A] R₁ :=
      IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := S) q.asIdeal
    let eR := e.toRingEquiv
    let I₀ := X.I.map (algebraMap X.A R₀)
    let I₁ := (X.I.map f).map (algebraMap (Localization S) R₁)
    let M₀ := LocalizedModule p₀.primeCompl X.M
    let MS := LocalizedModule S X.M
    let M₁ := LocalizedModule q.asIdeal.primeCompl MS
    let : RingHomInvPair eR.toRingHom eR.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv eR
    let : RingHomInvPair eR.symm.toRingHom eR.toRingHom :=
      RingHomInvPair.symm eR.toRingHom eR.symm.toRingHom
    let f₂ : MS →ₗ[Localization S] M₁ :=
      LocalizedModule.mkLinearMap q.asIdeal.primeCompl MS
    let : RingHomInvPair
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (M := S) q.asIdeal).toRingEquiv.toRingHom
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (M := S) q.asIdeal).toRingEquiv.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv eR
    let : RingHomInvPair
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (M := S) q.asIdeal).toRingEquiv.symm.toRingHom
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (M := S) q.asIdeal).toRingEquiv.toRingHom :=
      RingHomInvPair.symm eR.toRingHom eR.symm.toRingHom
    let fM : M₀ ≃ₛₗ[eR.toRingHom] M₁ :=
      localizedModule_localizationLocalizationEquiv (M := X.M) S q.asIdeal
    let : IsNoetherianRing R₀ :=
      IsLocalization.isNoetherianRing q₀.asIdeal.primeCompl R₀ inferInstance
    let : IsNoetherianRing R₁ :=
      IsLocalization.isNoetherianRing q.asIdeal.primeCompl R₁ inferInstance
    let : Module.Finite R₀ M₀ :=
      Module.Finite.of_isLocalizedModule q₀.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap q₀.asIdeal.primeCompl X.M)
    let : Module.Finite (Localization S) MS :=
      Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S X.M)
    let : Module.Finite R₁ M₁ :=
      Module.Finite.of_isLocalizedModule q.asIdeal.primeCompl f₂
    have hI : I₁ = I₀.map eR.toRingHom :=
      (map_map_localizationLocalizationAtPrimeIso S q.asIdeal X.I).symm
    let C₀ := AdicCompletion I₀ R₀
    let C₁ := AdicCompletion I₁ R₁
    let K₀ := AdicCompletion I₀ M₀
    let K₁ := AdicCompletion I₁ M₁
    let br := adicCompletion_ringEquiv I₀ I₁ eR hI
    let eC := br.equiv
    let : RingHomInvPair eC.toRingHom eC.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv eC
    let : RingHomInvPair eC.symm.toRingHom eC.toRingHom :=
      RingHomInvPair.symm eC.toRingHom eC.symm.toRingHom
    let J₀ := I₀.map (algebraMap R₀ C₀)
    let J₁ := I₁.map (algebraMap R₁ C₁)
    have hbase : eC.toRingHom.comp (algebraMap R₀ C₀) =
        (algebraMap R₁ C₁).comp eR.toRingHom := by
      apply RingHom.ext
      intro x
      exact br.map_base x
    have hmapC : ∀ K : Ideal R₀, (K.map eR.toRingHom).map (algebraMap R₁ C₁) =
        (K.map (algebraMap R₀ C₀)).map eC.toRingHom := fun K => by
      rw [Ideal.map_map, Ideal.map_map, hbase]
    have hJ : J₁ = J₀.map eC.toRingHom := by
      rw [← hmapC, ← hI]
    let eK : K₀ ≃ₛₗ[eC.toRingHom] K₁ :=
      adicCompletion_moduleSemilinearEquiv I₀ I₁ eR hI fM
    let p₁ := p'.asIdeal
    let p₀ := p₁.comap eC.toRingHom
    let : p₀.IsPrime := Ideal.comap_isPrime eC.toRingHom p₁
    let p₀spec : PrimeSpectrum C₀ := ⟨p₀, inferInstance⟩
    let m₀ := (maximalIdeal R₀).map (algebraMap R₀ C₀)
    let m₁ := (maximalIdeal R₁).map (algebraMap R₁ C₁)
    have hm : m₁ = m₀.map eC.toRingHom := by
      rw [← hmapC]
      exact congrArg (Ideal.map (algebraMap R₁ C₁))
        (IsLocalRing.map_ringEquiv_maximalIdeal eR).symm
    have hpm : p₁ = p₀.map eC.toRingHom := by
      change p₁ = (p₁.comap eC.toRingHom).map eC.toRingHom
      exact (Ideal.map_comap_of_surjective eC.toRingHom eC.surjective p₁).symm
    have hp₀not : ¬ J₀ ≤ p₀ := by
      intro hp₀
      have hp₁ : J₁ ≤ p₁ := by
        rw [hJ]
        exact (Ideal.map_le_iff_le_comap).2 hp₀
      exact hpnot hp₁
    have hcomap : ∀ {K₀ : Ideal C₀} {K₁ : Ideal C₁}, K₁ = K₀.map eC.toRingHom →
        K₀ = K₁.comap eC.toRingHom := fun h => by
      rw [h, Ideal.comap_map_of_bijective eC.toRingHom eC.bijective]
    have hm₀ : m₀ = m₁.comap eC.toRingHom := hcomap hm
    have hm₁prop : m₁.IsPrime ∧ p₁ ≤ m₁ ∧ J₁ ≤ m₁ := by
      have hmem : m₁ ∈ {r : Ideal C₁ | r.IsPrime ∧ p₁ ≤ r ∧ J₁ ≤ r} :=
        huniq.symm ▸ (Set.mem_singleton (m₁ : Ideal C₁))
      exact hmem
    have hJcomap : J₁.comap eC.toRingHom = J₀ := (hcomap hJ).symm
    have huniq₀ :
        {r : Ideal C₀ | r.IsPrime ∧ p₀ ≤ r ∧ J₀ ≤ r} = {m₀} := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hr, hpr, hJr⟩
        let : r.IsPrime := hr
        let r₁ := r.map eC.toRingHom
        have hr₁ : r₁.IsPrime := Ideal.map_isPrime_of_equiv eC
        have hp₁ : p₁ ≤ r₁ := by rw [hpm]; exact Ideal.map_mono hpr
        have hJ₁ : J₁ ≤ r₁ := by rw [hJ]; exact Ideal.map_mono hJr
        have hmem : r₁ ∈ {r : Ideal C₁ | r.IsPrime ∧ p₁ ≤ r ∧ J₁ ≤ r} :=
          ⟨hr₁, hp₁, hJ₁⟩
        have hrEq : r₁ = m₁ := by
          have := congrArg (fun U : Set (Ideal C₁) => r₁ ∈ U) huniq
          simpa using this.mp hmem
        calc
          r = (r.map eC.toRingHom).map eC.symm.toRingHom :=
            (Ideal.map_of_equiv eC).symm
          _ = m₁.map eC.symm.toRingHom := congrArg (Ideal.map eC.symm.toRingHom) hrEq
          _ = m₀ := by
            rw [hm]
            exact Ideal.map_of_equiv eC
      · rintro rfl
        refine ⟨?_, ?_, ?_⟩
        · rw [hm₀]
          let : m₁.IsPrime := hm₁prop.1
          exact Ideal.comap_isPrime eC.toRingHom m₁
        · rw [hm₀]
          exact Ideal.comap_mono hm₁prop.2.1
        · rw [hm₀, ← hJcomap]
          exact Ideal.comap_mono hm₁prop.2.2
    have hOrig := X.completedLocalDepth q₀ hq p₀spec hp₀not huniq₀
    have hOrigDepth :
        enatToEInt
          (Module.depth (Localization.AtPrime p₀spec.asIdeal)
            (maximalIdeal (Localization.AtPrime p₀spec.asIdeal))
            (LocalizedModule p₀spec.asIdeal.primeCompl K₀)) > (X.s : EInt) := by
      simpa [R₀, I₀, M₀, C₀, K₀, J₀, p₀spec] using hOrig
    let hpcomp : Submonoid.map eC.toMonoidHom p₀.primeCompl = p₁.primeCompl :=
      RingEquiv.map_primeCompl_comap_eq eC p₁
    let eLoc := IsLocalization.ringEquivOfRingEquiv
      (Localization p₀.primeCompl) (Localization p₁.primeCompl) eC hpcomp
    let : RingHomInvPair eLoc.toRingHom eLoc.symm.toRingHom :=
      RingHomInvPair.of_ringEquiv eLoc
    let : RingHomInvPair eLoc.symm.toRingHom eLoc.toRingHom :=
      RingHomInvPair.symm eLoc.toRingHom eLoc.symm.toRingHom
    let eLocM := localizedModuleSemilinearEquiv p₀ p₁ eC (by
      exact hpm) hpcomp eK
    have hmaxLoc : (maximalIdeal (Localization p₁.primeCompl)) =
        (maximalIdeal (Localization p₀.primeCompl)).map eLoc.toRingHom := by
      symm
      exact IsLocalRing.map_ringEquiv_maximalIdeal eLoc
    have hdepthLoc := depth_eq_of_ringModuleSemilinearEquiv eLoc
      (maximalIdeal (Localization p₀.primeCompl))
      (maximalIdeal (Localization p₁.primeCompl)) eLocM hmaxLoc
    have hTargetDepth :
        enatToEInt
          (Module.depth (Localization p₁.primeCompl) (maximalIdeal (Localization p₁.primeCompl))
            (LocalizedModule p₁.primeCompl K₁)) > (X.s : EInt) := by
      rw [← hdepthLoc]
      simpa [R₀, R₁, I₀, I₁, M₀, M₁, C₀, C₁, K₀, K₁, p₀spec, p₀, p₁] using hOrigDepth
    simpa [Localization.AtPrime] using hTargetDepth

namespace BootstrapSituation

/-- **Stacks Project, Tag 0EFV, part (F).** The localization of a bootstrap situation at a
multiplicative subset `S ⊆ A`: the quadruple `S⁻¹A, S⁻¹I, T', S⁻¹M`, with `T'` the inverse image
of `T` in `V(S⁻¹I)`, again satisfies every assumption of Situation 0EFU, with the same bounds
`s` and `d`. -/
@[stacks 0EFV "part (F): for a multiplicative subset S ⊆ A the quadruple S⁻¹A, S⁻¹I, T', S⁻¹M, \
with T' the inverse image of T, is again a situation as in Stacks 0EFU"]
public def localize
    (X : BootstrapSituation.{u, v, w}) (S : Submonoid X.A) :
    BootstrapSituation.{u, max u v, w} := by
  letI : IsNoetherianRing (Localization S) :=
    IsLocalization.isNoetherianRing S (Localization S) inferInstance
  letI : Module.Finite (Localization S) (LocalizedModule S X.M) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S X.M)
  exact {
    A := Localization S
    I := X.I.map (algebraMap X.A (Localization S))
    M := LocalizedModule S X.M
    T := locus X S
    subset_adicLocus := subset_adicLocus_localization X S
    stableUnderSpecialization := stableUnderSpecialization_localization X S
    s := X.s
    d := X.d
    dualizing := dualizing_localization X S
    cohomologicalDimension_le :=
      cohomologicalDimension_le_localization X S
    depth_or_depth_add_dimension :=
      depth_or_depth_add_dimension_localization X S
    completedLocalDepth := completedLocalDepth_localization X S }

end BootstrapSituation

end Stacks.Algebraization

end
