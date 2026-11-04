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
public import StacksFrontier.RingTheory.Branches.Miscellaneous.SmoothInvariance
import StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapAtGenericFibre
import StacksFrontier.RingTheory.AdicCompletion.FiniteBaseChange
import StacksFrontier.RingTheory.Branches.Completion
import StacksFrontier.RingTheory.Henselian.StrictHenselization.Quotient

@[expose] public section

/-!
# Branches: étale neighbourhoods of unramified points over unibranch domains

Let `A` be a domain, let `q` be a prime of an `A`-algebra `B` lying over a prime `p` of `A`, and
suppose that `Aₚ` is geometrically unibranch, that `A → B` is unramified at `q`, and that
`Aₚ → B_q` is injective. Then some principal localization `B_g` with `g ∉ q` is étale over `A`.

## Main results

* `exists_etale_away_of_isGeometricallyUnibranch_of_isUnramifiedAt` (Stacks 0GSC): the principal
  étale neighbourhood of an unramified point over a geometrically unibranch domain.

## Implementation notes

Unramifiedness at a prime uses the neighbourhood condition of Stacks Definition 00UT(3): some
`B_f` with `f ∉ q` is unramified over the base. The auxiliary
`isUnibranch_of_isLocalization_smooth` and `isDomain_localizationAtPrime_of_etale` used for
Tag 0GSC take their rings in one universe, which is all Tag 0GSC needs of them. Tag 0GSC is
stated in full generality.

## References

* [The Stacks Project, Tag 0GSC](https://stacks.math.columbia.edu/tag/0GSC)
-/

universe u v w uA uB uC uN vA vB

section UnramifiedNeighborhood

open IsLocalRing

private lemma exists_henselizations (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (Rh Rsh : Type u) (_ : CommRing Rh) (_ : CommRing Rsh)
      (_ : IsLocalRing Rh) (_ : IsLocalRing Rsh) (_ : Algebra R Rh) (_ : Algebra R Rsh),
      IsHenselization R (ResidueField R) Rh ∧
      IsHenselization R (SeparableClosure (ResidueField R)) Rsh := by
  obtain ⟨Rh, _, _, _, _, hh, hi, hm, hr⟩ := exists_henselization R
  obtain ⟨Rsh, _, _, _, _, _, _, hsh, -, hsi, -, hsres⟩ :=
    exists_strictHenselization R Rh hi hr.2 (SeparableClosure (ResidueField R))
  refine ⟨Rh, Rsh, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, IsHenselization.of_ind_etale.{u, u, u} hh hi ?_,
    IsHenselization.of_ind_etale.{u, u, u} hsh hsi hsres⟩
  refine ⟨RingEquiv.ofBijective (ResidueField.map (algebraMap R Rh)) hr, ?_⟩
  intro x
  exact ResidueField.map_residue (algebraMap R Rh) x

private lemma isUnibranch_of_isLocalization_smooth
    (A B : Type u) [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hgeom : IsGeometricallyUnibranch A)
    (hsm : ∃ (C : Type w) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (S : Submonoid C),
        Algebra.Smooth A C ∧ IsLocalization S B) :
    IsUnibranch B := by
  obtain ⟨Ah, Ash, _, _, _, _, _, _, hh, hsh⟩ := exists_henselizations A
  obtain ⟨Bh, Bsh, _, _, _, _, _, _, kh, ksh⟩ := exists_henselizations B
  let := hh
  let := hsh
  let := kh
  let := ksh
  have hA := (numberOfBranches_characterizations A Ah Ash
    (SeparableClosure (ResidueField A))).2.2.1.mpr hgeom
  have hAB := (numberOfBranches_eq_of_isLocalization_smooth
    A Ah Ash B Bh Bsh (SeparableClosure (ResidueField A))
    (SeparableClosure (ResidueField B)) hsm).1
  exact ((numberOfBranches_characterizations B Bh Bsh
    (SeparableClosure (ResidueField B))).2.2.1.mp (hAB ▸ hA)).1

private lemma isDomain_of_isReduced_of_isUnibranch
    (R : Type u) [CommRing R] [IsLocalRing R] [IsReduced R]
    (h : IsUnibranch R) : IsDomain R := by
  have : IsDomain (R ⧸ nilradical R) := h.1
  exact Function.Injective.isDomain (Ideal.Quotient.mk (nilradical R))
    (by rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker]; exact nilradical_eq_zero R)

private lemma finite_minimalPrimes_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsNoetherianRing S]
    (f : R →+* S) (hf : Function.Injective f) : (minimalPrimes R).Finite := by
  have hk : Ideal.comap f ⊥ = ⊥ := (RingHom.injective_iff_ker_eq_bot f).mp hf
  have h := Ideal.minimalPrimes_comap_subset f (⊥ : Ideal S)
  rw [hk] at h
  exact ((minimalPrimes.finite_of_isNoetherianRing S).image (Ideal.comap f)).subset h

private lemma finite_minimalPrimes_of_flat_finiteType
    (A : Type u) (C : Type v) [CommRing A] [CommRing C] [IsDomain A]
    [Algebra A C] [Module.Flat A C] [Algebra.FiniteType A C] :
    (minimalPrimes C).Finite := by
  let K := FractionRing A
  let T := TensorProduct A K C
  have : Algebra.FiniteType K T := Algebra.FiniteType.baseChange K
  have : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  exact finite_minimalPrimes_of_injective
    (Algebra.TensorProduct.includeRight : C →ₐ[A] T).toRingHom
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective A K))

private lemma minimalPrime_eq_ker_of_le
    {R : Type u} [CommRing R] (q : Ideal R) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] {r : Ideal R}
    (hr : r ∈ minimalPrimes R) (hrq : r ≤ q) :
    r = RingHom.ker (algebraMap R (Localization.AtPrime q)) := by
  let S := Localization.AtPrime q
  have hd : Disjoint (q.primeCompl : Set R) r :=
    Set.disjoint_left.mpr fun x hx hxr => hx (hrq hxr)
  have he := IsLocalization.under_map_of_isPrime_disjoint q.primeCompl S hr.1.1 hd
  have hm : r.map (algebraMap R S) ∈ minimalPrimes S := by
    show r.map (algebraMap R S) ∈ (⊥ : Ideal S).minimalPrimes
    rw [← Ideal.map_bot (f := algebraMap R S),
      IsLocalization.minimalPrimes_map q.primeCompl S, Set.mem_preimage, he]
    exact hr
  rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff] at hm
  rw [hm] at he
  exact he.symm

private lemma exists_notMem_annihilates_ker_localizationAtPrime
    {R : Type u} [CommRing R] [IsReduced R] (q : Ideal R) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] (hfin : (minimalPrimes R).Finite) :
    ∃ s : R, s ∉ q ∧ ∀ x : R, algebraMap R (Localization.AtPrime q) x = 0 → s * x = 0 := by
  classical
  let t := hfin.toFinset.filter (fun r => ¬ r ≤ q)
  have hex (r : {r // r ∈ t}) : ∃ a : R, a ∈ r.1 ∧ a ∉ q :=
    SetLike.not_le_iff_exists.mp (Finset.mem_filter.mp r.2).2
  choose a ha using hex
  let s := ∏ r : {r // r ∈ t}, a r
  refine ⟨s, ?_, ?_⟩
  · exact (show s ∈ q.primeCompl from prod_mem fun r _ => (ha r).2)
  · intro x hx
    have hm : s * x ∈ sInf (minimalPrimes R) := by
      apply Ideal.mem_sInf.mpr
      intro r hr
      by_cases hrq : r ≤ q
      · have hxr : x ∈ r := by
          rw [minimalPrime_eq_ker_of_le q hr hrq]
          exact hx
        exact r.mul_mem_left s hxr
      · have hrt : r ∈ t := Finset.mem_filter.mpr ⟨hfin.mem_toFinset.mpr hr, hrq⟩
        have hsr : s ∈ r := r.prod_mem (i := ⟨r, hrt⟩) (Finset.mem_univ _) (ha ⟨r, hrt⟩).1
        exact r.mul_mem_right x hsr
    simpa only [Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced, Ideal.mem_bot] using hm

private lemma isDomain_localizationAtPrime_of_etale
    (A C : Type u) [CommRing A] [CommRing C] [IsReduced A]
    [Algebra A C] [Algebra.Etale A C] (p : Ideal A) [p.IsPrime]
    (q : Ideal C) [q.IsPrime] [q.LiesOver p]
    (hgeom : IsGeometricallyUnibranch (Localization.AtPrime p)) :
    IsDomain (Localization.AtPrime q) := by
  let Ap := Localization.AtPrime p
  let Cq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : IsReduced C := Algebra.isReduced_of_smooth A C
  have : IsReduced Cq := inferInstance
  apply isDomain_of_isReduced_of_isUnibranch Cq
  apply isUnibranch_of_isLocalization_smooth Ap Cq hgeom
  let T := TensorProduct A Ap C
  let : Algebra C T := Algebra.TensorProduct.rightAlgebra
  let φ : T →ₐ[A] Cq := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom A Ap Cq) (IsScalarTower.toAlgHom A C Cq)
    (fun _ _ => Commute.all _ _)
  let : Algebra T Cq := φ.toRingHom.toAlgebra
  have : IsScalarTower Ap T Cq :=
    IsScalarTower.of_algebraMap_eq' (R := Ap) (S := T) (A := Cq) <| by
      ext a
      show algebraMap Ap Cq a = φ (a ⊗ₜ[A] (1 : C))
      dsimp only [φ]
      rw [Algebra.TensorProduct.lift_tmul]
      simp
  have : IsScalarTower C T Cq :=
    IsScalarTower.of_algebraMap_eq' (R := C) (S := T) (A := Cq) <| by
      ext c
      show algebraMap C Cq c = φ ((1 : Ap) ⊗ₜ[A] c)
      dsimp only [φ]
      rw [Algebra.TensorProduct.lift_tmul]
      simp
  have hle : Algebra.algebraMapSubmonoid C p.primeCompl ≤ q.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩
    exact fun h => ha ((q.over_def p ▸ h : a ∈ p))
  have : IsLocalization
      (Algebra.algebraMapSubmonoid T q.primeCompl) Cq :=
    IsLocalization.isLocalization_of_submonoid_le T Cq
      (Algebra.algebraMapSubmonoid C p.primeCompl) q.primeCompl hle
  exact ⟨T, inferInstance, inferInstance, inferInstance, inferInstance,
    Algebra.algebraMapSubmonoid T q.primeCompl, inferInstance, inferInstance⟩

private lemma exists_etale_away_of_notMem_map
    {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    (g : S) [IsLocalization.Away g T] (Q : Ideal S) [Q.IsPrime] (hg : g ∉ Q)
    {f : T} (hf : f ∉ Q.map (algebraMap S T)) [Algebra.Etale R (Localization.Away f)] :
    ∃ h : S, h ∉ Q ∧ Algebra.Etale R (Localization.Away h) := by
  obtain ⟨a, hassoc⟩ : ∃ a : S, Associated (algebraMap S T a) f :=
    ⟨_, IsLocalization.Away.associated_sec_fst g f⟩
  have : IsLocalization.Away (g * a) (Localization.Away f) :=
    IsLocalization.Away.mul_of_associated (S := T) g a f hassoc
  refine ⟨g * a, ‹Q.IsPrime›.mul_notMem hg (fun ha => ?_), ?_⟩
  · exact hf ((Ideal.mem_iff_of_associated hassoc).1 (Ideal.mem_map_of_mem _ ha))
  · exact Algebra.Etale.of_equiv
      ((IsLocalization.algEquiv (.powers (g * a)) (Localization.Away f)
        (Localization.Away (g * a))).restrictScalars R)

/-- Let `A → B` be a ring map from a domain, and let `q` be a prime of `B` lying over a prime
`p` of `A`. If `Aₚ` is geometrically unibranch, the map is unramified at `q`, and the canonical
map `Aₚ → B_q` is injective, then some principal localization `B_g`, with `g ∉ q`, is étale
over `A`. -/
@[stacks 0GSC, ega "IV 18.10.1" "(i)+(ii) ⇒ étale"]
theorem exists_etale_away_of_isGeometricallyUnibranch_of_isUnramifiedAt
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] [q.LiesOver p]
    (hgeom : IsGeometricallyUnibranch (Localization.AtPrime p))
    (hunram : ∃ f : B, f ∉ q ∧ Algebra.Unramified A (Localization.Away f))
    (hinj : letI := Localization.AtPrime.algebraOfLiesOver p q
      Function.Injective
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))) :
    ∃ g : B, g ∉ q ∧ Algebra.Etale A (Localization.Away g) := by
  obtain ⟨g, hg, P, φ, hφ⟩ :=
    Algebra.exists_hasStandardEtaleSurjectionOn_of_exists_unramified q hunram
  let D := Localization.Away g
  let qD : Ideal D := q.map (algebraMap B D)
  have hdis : Disjoint ((Submonoid.powers g : Submonoid B) : Set B) q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hg
  have : qD.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers g) D q inferInstance hdis
  have hqD : qD.under B = q :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers g) D inferInstance hdis
  have : qD.LiesOver q := ⟨hqD.symm⟩
  have : qD.LiesOver p := .trans _ q _
  let Dq := Localization.AtPrime qD
  have : IsLocalization.AtPrime Dq q := by
    have hloc : IsLocalization.AtPrime Dq (qD.under B) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (.powers g) Dq qD
    simpa only [hqD] using hloc
  let e : Localization.AtPrime q ≃ₐ[B] Dq :=
    IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) Dq
  have hAinj : Function.Injective (algebraMap A Dq) := by
    let := Localization.AtPrime.algebraOfLiesOver p q
    have hi : Function.Injective (algebraMap A (Localization.AtPrime q)) := by
      rw [IsScalarTower.algebraMap_eq A (Localization.AtPrime p) (Localization.AtPrime q)]
      exact hinj.comp (IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors)
    have he : algebraMap A Dq = e.toRingHom.comp (algebraMap A (Localization.AtPrime q)) := by
      ext a
      exact (e.restrictScalars A).commutes a |>.symm
    rw [he]
    exact e.injective.comp hi
  let C := P.Ring
  let qC : Ideal C := qD.comap φ.toRingHom
  have : qC.IsPrime := Ideal.comap_isPrime φ.toRingHom qD
  have : qC.LiesOver p := ⟨by
    show p = Ideal.comap (algebraMap A C) (qD.comap φ.toRingHom)
    rw [Ideal.comap_comap]
    erw [φ.comp_algebraMap]
    exact qD.over_def p⟩
  let Cq := Localization.AtPrime qC
  have : IsDomain Cq := isDomain_localizationAtPrime_of_etale A C p qC hgeom
  let ψ : Cq →ₐ[A] Dq := Localization.localAlgHom qC qD φ rfl
  have hψ : Function.Injective ψ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hker
    have hcon := comap_ne_bot_of_localization_or_discrete_fibers A Cq
      (Or.inl ⟨C, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, qC.primeCompl, inferInstance⟩) (RingHom.ker ψ.toRingHom) hker
    apply hcon
    show RingHom.ker (ψ.toRingHom.comp (algebraMap A Cq)) = ⊥
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hAinj
  have : IsReduced C := Algebra.isReduced_of_smooth A C
  obtain ⟨s, hs, hkill⟩ := exists_notMem_annihilates_ker_localizationAtPrime qC
    (finite_minimalPrimes_of_flat_finiteType A C)
  have hkerφ (x : C) (hx : φ x = 0) : s * x = 0 := by
    apply hkill x
    apply hψ
    show Localization.localRingHom qC qD φ.toRingHom rfl
      (algebraMap C Cq x) = ψ 0
    rw [Localization.localRingHom_to_map]
    show algebraMap D Dq (φ x) = ψ 0
    rw [hx, map_zero, map_zero]
  let θ : Localization.Away s →ₐ[A] Localization.Away (φ s) :=
    IsLocalization.Away.mapₐ _ _ φ s
  have hθ : Function.Bijective θ :=
    ⟨(IsLocalization.Away.map_injective_iff (Localization.Away (φ s)) φ.toRingHom s).mpr
      fun x hx => ⟨1, by simpa using hkerφ x hx⟩,
      IsLocalization.Away.mapₐ_surjective_of_surjective s hφ⟩
  have : Algebra.Etale A (Localization.Away (φ s)) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofBijective θ hθ)
  exact exists_etale_away_of_notMem_map g q hg hs

end UnramifiedNeighborhood

end
