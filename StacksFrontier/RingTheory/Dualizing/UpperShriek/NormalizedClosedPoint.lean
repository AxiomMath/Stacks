module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Normalized
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dimension function of an upper shriek at a maximal ideal

Let `φ : R → A` be a finite type homomorphism of Noetherian rings, `K` a dualizing complex over
`R`, and `m ⊆ A` a maximal ideal lying over the prime `q ⊆ R`. Then the dimension function of
`φ^!(K)` at `m` equals that of `K` at `q`. For `R` local, `q` maximal and `K` normalized this is
[Stacks, Tag 0E9N]; the general statement is what the proofs of [Stacks, Tag 0AWL] and
[Stacks, Tag 0AWM] use at a closed point of an affine scheme of finite type over a Noetherian
scheme.

## Main results

* `Dualizing.ringKrullDim_localizationAtPrime_mvPolynomial_of_isMaximal` —
  `dim(R[x_1, …, x_n]_m) = ht(q) + n` for `m` maximal and `q = m ∩ R`.
* `Dualizing.PolynomialPresentation.dualizingDimension_derivedExtension_of_isMaximal` — the
  polynomial step.
* `Dualizing.PolynomialPresentation.dualizingDimension_upperShriekFunctor_of_isMaximal` — the
  dimension function of `φ^!(K)` at `m` is that of `K` at `q`.

## References

* [Stacks Project, Tag 0E9N](https://stacks.math.columbia.edu/tag/0E9N)
* [Stacks Project, Tag 0AWL](https://stacks.math.columbia.edu/tag/0AWL)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The case of `ringKrullDim_localizationAtPrime_mvPolynomial_of_isMaximal` where `q` is
maximal: the fibre `κ(q)[x_1, …, x_n]` has all its maximal ideals of height `n`. -/
@[ega "IV 5.5.3" "special case", ega "IV 5.6.11" "partial"]
private theorem ringKrullDim_localizationAtPrime_mvPolynomial_of_isMaximal_aux
    {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ) (q : Ideal R) [q.IsMaximal]
    (m : Ideal (MvPolynomial (Fin n) R)) [m.IsMaximal]
    (hlies : m.comap (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) = q)
    (d : ℕ) (hd : q.height = (d : ℕ∞)) :
    ringKrullDim (Localization.AtPrime m) = ((d + n : ℕ) : WithBot ℕ∞) := by
  have halg : (algebraMap R (MvPolynomial (Fin n) R))
      = (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) := MvPolynomial.algebraMap_eq R (Fin n)
  have hliesover : m.LiesOver q := ⟨by rw [Ideal.under_def, halg, hlies]⟩
  have hgd : Algebra.HasGoingDown R (MvPolynomial (Fin n) R) := Algebra.HasGoingDown.of_flat
  have hfibre : (m.map (Ideal.Quotient.mk (Ideal.map
      (algebraMap R (MvPolynomial (Fin n) R)) q))).height = (n : ℕ∞) := by
    rw [halg]
    have hMmax : (m.map (Ideal.Quotient.mk (Ideal.map
        (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) q))).IsMaximal := by
      refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
      rw [Ideal.mk_ker, Ideal.map_le_iff_le_comap, hlies]
    have he : (MvPolynomial (Fin n) R ⧸ Ideal.map
        (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) q) ≃+*
        MvPolynomial (Fin n) (R ⧸ q) :=
      (MvPolynomial.quotientEquivQuotientMvPolynomial q).symm.toRingEquiv
    have hMemax : (Ideal.map he (m.map (Ideal.Quotient.mk (Ideal.map
        (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) q)))).IsMaximal := inferInstance
    rw [← he.height_map]
    exact @height_maximal_ideal_eq (R ⧸ q) (Ideal.Quotient.field _) n _ hMemax
  have hsplit := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (R := R) (S := MvPolynomial (Fin n) R) q m
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), hsplit,
    hd, hfibre]
  push_cast
  rfl

/-- **The dimension of a polynomial ring localized at a maximal ideal.** Let `R` be Noetherian,
`m` a maximal ideal of `R[x_1, …, x_n]` and `q = m ∩ R`, of height `d`. Then
`dim(R[x_1, …, x_n]_m) = d + n`. -/
@[ega "IV 10.7.3" "partial", ega "IV 5.5.3" "special case"]
theorem ringKrullDim_localizationAtPrime_mvPolynomial_of_isMaximal
    {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ) (q : Ideal R) [q.IsPrime]
    (m : Ideal (MvPolynomial (Fin n) R)) [m.IsMaximal]
    (hlies : m.comap (MvPolynomial.C : R →+* MvPolynomial (Fin n) R) = q)
    (d : ℕ) (hd : q.height = (d : ℕ∞)) :
    ringKrullDim (Localization.AtPrime m) = ((d + n : ℕ) : WithBot ℕ∞) := by
  let Rq := Localization.AtPrime q
  have : IsNoetherianRing Rq := IsLocalization.isNoetherianRing q.primeCompl Rq inferInstance
  let := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := R) (S := Rq)
  let Mq : Submonoid (MvPolynomial (Fin n) R) := q.primeCompl.map MvPolynomial.C
  have : IsLocalization Mq (MvPolynomial (Fin n) Rq) := MvPolynomial.isLocalization _ _
  have hdisj : Disjoint (Mq : Set (MvPolynomial (Fin n) R))
      (m : Set (MvPolynomial (Fin n) R)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hm
    exact hr (hlies ▸ (show r ∈ m.comap MvPolynomial.C from hm))
  let m' := m.map (algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) Rq))
  have hm' : m'.IsMaximal := IsLocalization.isMaximal_of_isMaximal_disjoint Mq _ m hdisj
  have hheight : m'.height = m.height := IsLocalization.height_map_of_disjoint Mq m hdisj
  have hcomap : m'.comap (MvPolynomial.C : Rq →+* MvPolynomial (Fin n) Rq) =
      IsLocalRing.maximalIdeal Rq := by
    refine ((IsLocalRing.maximalIdeal.isMaximal Rq).eq_of_le
      (Ideal.comap_isPrime _ m').ne_top ?_).symm
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q Rq, Ideal.map_le_iff_le_comap]
    intro r hr
    show MvPolynomial.C (algebraMap R Rq r) ∈ m'
    have : MvPolynomial.C (algebraMap R Rq r) =
        algebraMap (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) Rq) (MvPolynomial.C r) := by
      rw [MvPolynomial.algebraMap_def, MvPolynomial.map_C]
    rw [this]
    exact Ideal.mem_map_of_mem _ (show r ∈ m.comap MvPolynomial.C from hlies ▸ hr)
  have hdq : (IsLocalRing.maximalIdeal Rq).height = (d : ℕ∞) := by
    rwa [← IsLocalization.height_under q.primeCompl (IsLocalRing.maximalIdeal Rq),
      IsLocalization.AtPrime.under_maximalIdeal Rq q]
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), ← hheight,
    ← IsLocalization.AtPrime.ringKrullDim_eq_height m' (Localization.AtPrime m')]
  exact ringKrullDim_localizationAtPrime_mvPolynomial_of_isMaximal_aux n
    (IsLocalRing.maximalIdeal Rq) m' hcomap d hdq

/-- The map `R_q → P_m` induced by `MvPolynomial.C` makes `P_m` faithfully flat over `R_q`. -/
private theorem PolynomialPresentation.faithfullyFlat_localRingHom
    {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}
    (p : PolynomialPresentation f) (q : Ideal R) [q.IsPrime] (m : Ideal p.Poly) [m.IsPrime]
    (hlies : m.comap (MvPolynomial.C : R →+* p.Poly) = q) :
    letI := (Localization.localRingHom q m (MvPolynomial.C : R →+* p.Poly) hlies.symm).toAlgebra
    Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime m) := by
  set g := Localization.localRingHom q m (MvPolynomial.C : R →+* p.Poly) hlies.symm
  have : IsLocalHom g := Localization.isLocalHom_localRingHom q m _ hlies.symm
  let := g.toAlgebra
  have : Module.Flat p.Poly (Localization.AtPrime m) := IsLocalization.flat _ m.primeCompl
  have hflat : Module.Flat R (Localization.AtPrime m) := Module.Flat.trans R p.Poly _
  have : IsScalarTower R (Localization.AtPrime q) (Localization.AtPrime m) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      show _ = g (algebraMap R _ r)
      rw [Localization.localRingHom_to_map,
        IsScalarTower.algebraMap_apply R p.Poly (Localization.AtPrime m),
        MvPolynomial.algebraMap_eq]
  have : Module.Flat (Localization.AtPrime q) (Localization.AtPrime m) :=
    (Module.flat_iff_of_isLocalization _ q.primeCompl (M := Localization.AtPrime m)).mpr hflat
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The homology of the localization at `m` of `K ⊗_R^L R[x_1, …, x_n]` is the base change along
`R_q → P_m` of the homology of `K ⊗_R^L R_q`. -/
private noncomputable def PolynomialPresentation.homologyDerivedExtensionLocalizationIso
    {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}
    (p : PolynomialPresentation f) (q : Ideal R) [q.IsPrime] (m : Ideal p.Poly) [m.IsPrime]
    (hlies : m.comap (MvPolynomial.C : R →+* p.Poly) = q)
    (K : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.AtPrime m)) i).obj
        ((StacksDraft.PseudoCoherence.derivedExtensionScalars
          (algebraMap p.Poly (Localization.AtPrime m))).obj (p.derivedExtension.{u, u}.obj K)) ≅
      (ModuleCat.extendScalars
          (Localization.localRingHom q m (MvPolynomial.C : R →+* p.Poly) hlies.symm)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Localization.AtPrime q)) i).obj
          ((StacksDraft.PseudoCoherence.derivedExtensionScalars
            (algebraMap R (Localization.AtPrime q))).obj K)) := by
  set g := Localization.localRingHom q m (MvPolynomial.C : R →+* p.Poly) hlies.symm
  have hg : g.comp (algebraMap R (Localization.AtPrime q)) =
      (algebraMap p.Poly (Localization.AtPrime m)).comp MvPolynomial.C :=
    RingHom.ext (Localization.localRingHom_to_map q m _ hlies.symm)
  refine derivedExtensionScalarsHomologyObjIso (algebraMap p.Poly _)
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ m.primeCompl)) _ i ≪≫ ?_
  refine (ModuleCat.extendScalars (algebraMap p.Poly _)).mapIso
    (p.derivedExtensionHomologyIso.{u, u} K i) ≪≫ ?_
  refine ((ModuleCat.extendScalarsComp (MvPolynomial.C : R →+* p.Poly)
    (algebraMap p.Poly (Localization.AtPrime m))).app
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)).symm ≪≫ ?_
  refine eqToIso (congrArg (fun φ => (ModuleCat.extendScalars φ).obj
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) hg.symm) ≪≫ ?_
  refine (ModuleCat.extendScalarsComp (algebraMap R (Localization.AtPrime q)) g).app _ ≪≫ ?_
  exact (ModuleCat.extendScalars g).mapIso (derivedExtensionScalarsHomologyObjIso _
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ q.primeCompl)) K i).symm

/-- **The polynomial step at a maximal ideal.** Let `R` be Noetherian with a dualizing complex
`K`, let `p` be a polynomial presentation with `n` variables and let `m` be a maximal ideal of its
polynomial algebra lying over the prime `q` of `R`. Then the dimension
function of `K ⊗_R^L R[x_1, …, x_n]` at `m` is that of `K` at `q` minus `n`. -/
theorem PolynomialPresentation.dualizingDimension_derivedExtension_of_isMaximal
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] {f : R →+* A}
    (p : PolynomialPresentation f) (q : Ideal R) [q.IsPrime] (m : Ideal p.Poly) [m.IsMaximal]
    (hlies : m.comap (MvPolynomial.C : R →+* p.Poly) = q)
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsDualizingComplex K) :
    dualizingDimension.{u, u} (p.derivedExtension.{u, u}.obj K)
        (⟨m, inferInstance⟩ : PrimeSpectrum p.Poly) =
      dualizingDimension.{u, u} K (⟨q, inferInstance⟩ : PrimeSpectrum R) -
        (p.variableCount : ℤ) := by
  set δ := dualizingDimension.{u, u} K (⟨q, inferInstance⟩ : PrimeSpectrum R)
  set Rq := Localization.AtPrime q
  set Pm := Localization.AtPrime m
  -- the normalized localization of `K` at `q`
  have : IsNoetherianRing Rq := IsLocalization.isNoetherianRing q.primeCompl Rq inferInstance
  obtain ⟨d, hd⟩ := Stacks.RegularLocalRing.KernelRegularity.exists_natCast_eq_ringKrullDim Rq
  have hqheight : q.height = (d : ℕ∞) := by
    have h := IsLocalization.AtPrime.ringKrullDim_eq_height q Rq
    rw [hd] at h
    exact_mod_cast h.symm
  have hnormq := dualizingDimension_spec.{u, u} K hK (⟨q, inferInstance⟩ : PrimeSpectrum R)
  have : IsNoetherianRing Pm := IsLocalization.isNoetherianRing m.primeCompl Pm inferInstance
  have hL : IsDualizingComplex (p.derivedExtension.{u, u}.obj K) :=
    mvPolynomialBaseChange_isDualizingComplex p.variableCount K hK
  have hLB : IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap p.Poly Pm)).obj
        (p.derivedExtension.{u, u}.obj K)) :=
    isDualizingComplex_localization m.primeCompl _ hL
  let g : Rq →+* Pm := Localization.localRingHom q m (MvPolynomial.C : R →+* p.Poly) hlies.symm
  let := g.toAlgebra
  have hff : Module.FaithfullyFlat Rq Pm := p.faithfullyFlat_localRingHom q m hlies
  have hcomp := p.homologyDerivedExtensionLocalizationIso q m hlies K
  have hdim := ringKrullDim_localizationAtPrime_mvPolynomial_of_isMaximal p.variableCount q m
    hlies d hqheight
  -- the shift of the localized base change by `n - δ` is normalized
  have hnorm : IsNormalizedDualizingComplex.{u, u}
      (((StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap p.Poly Pm)).obj
        (p.derivedExtension.{u, u}.obj K))⟦-(δ - (p.variableCount : ℤ))⟧) := by
    set M := (StacksDraft.PseudoCoherence.derivedExtensionScalars (algebraMap R Rq)).obj K
    refine isNormalizedDualizingComplex_of_homology_bounds.{u} _
      (isDualizingComplex_shift _ hLB _) (d + p.variableCount) hdim (fun i hi => ?_) ?_
    · refine .of_iso (.of_iso (Functor.map_isZero _ ?_) (hcomp _)) (homologyShiftIso.{u} _ _ i)
      refine .of_iso (isZero_homology_of_lt_neg_ringKrullDim.{u} (M⟦-δ⟧) hnormq d hd
        ((p.variableCount : ℤ) + i) (by push_cast at hi; omega)) ?_
      refine eqToIso ?_ ≪≫ (homologyShiftIso.{u} M (-δ) _).symm
      congr 2
      omega
    · have hnt := nontrivial_homology_neg_ringKrullDim.{u} (M⟦-δ⟧) hnormq d hd
      have hnt' := (homologyShiftIso.{u} M (-δ) _).toLinearEquiv.toEquiv.nontrivial_congr.mp hnt
      have htensor : Nontrivial (TensorProduct Rq Pm
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} Rq) (-δ + -(d : ℤ))).obj M)) :=
        (Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right Rq Pm).mpr hnt'
      have hext := (extendCarrierEquiv.{u, u} _).toEquiv.nontrivial_congr.mp htensor
      refine (homologyShiftIso.{u} _ _ _).toLinearEquiv.toEquiv.nontrivial_congr.mpr ?_
      refine ((hcomp _).toLinearEquiv.toEquiv.nontrivial_congr).mpr ?_
      rwa [show -(δ - (p.variableCount : ℤ)) + -((d + p.variableCount : ℕ) : ℤ) = -δ + -(d : ℤ) by
        push_cast; ring]
  exact ((dualizingDimension_eq_iff.{u, u} _ hL (⟨m, inferInstance⟩ : PrimeSpectrum p.Poly)
    _).mp hnorm).symm

/-- **The dimension function of an upper shriek at a maximal ideal.** Let `φ : R → A` be a finite
type homomorphism of Noetherian rings presented by `p`, `K` a dualizing complex over `R`, and
`m ⊆ A` a maximal ideal lying over the prime `q ⊆ R`. Then the
dimension function of `φ^!(K)` at `m` is that of `K` at `q`. -/
theorem PolynomialPresentation.dualizingDimension_upperShriekFunctor_of_isMaximal
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R] [IsNoetherianRing A]
    {f : R →+* A} (p : PolynomialPresentation f) (m : Ideal A) [m.IsMaximal] (q : Ideal R)
    [q.IsPrime] (hlies : m.comap f = q)
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : IsDualizingComplex K) :
    dualizingDimension.{u, u} (p.upperShriekFunctor.{u, u}.obj K)
        (⟨m, inferInstance⟩ : PrimeSpectrum A) =
      dualizingDimension.{u, u} K (⟨q, inferInstance⟩ : PrimeSpectrum R) := by
  have hm' : (m.comap p.toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ p.surjective
  have hlies' : (m.comap p.toRingHom).comap (MvPolynomial.C : R →+* p.Poly) = q := by
    rwa [Ideal.comap_comap, p.commutes]
  have hL : IsDualizingComplex (p.derivedExtension.{u, u}.obj K) :=
    mvPolynomialBaseChange_isDualizingComplex p.variableCount K hK
  have hZ : IsDualizingComplex
      ((derivedHom.{u, u} p.toRingHom).obj (p.derivedExtension.{u, u}.obj K)) :=
    isDualizingComplex_derivedHom_of_finite.{u, u} p.toRingHom p.finite_toRingHom _ hL
  rw [p.upperShriekFunctor_obj.{u, u} K,
    dualizingDimension_shift.{u} _ hZ (⟨m, inferInstance⟩ : PrimeSpectrum A)
      (p.variableCount : ℤ),
    dualizingDimension_derivedHom_of_surjective.{u, u} p.toRingHom p.surjective
      (p.derivedExtension.{u, u}.obj K) hL (⟨m, inferInstance⟩ : PrimeSpectrum A)]
  show dualizingDimension.{u, u} (p.derivedExtension.{u, u}.obj K)
      (⟨m.comap p.toRingHom, inferInstance⟩ : PrimeSpectrum p.Poly) + _ = _
  rw [p.dualizingDimension_derivedExtension_of_isMaximal q (m.comap p.toRingHom) hlies' K hK]
  ring

end Dualizing
