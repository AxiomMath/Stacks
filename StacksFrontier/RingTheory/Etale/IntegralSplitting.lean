module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Adjoin.FGBaseChange
public import Mathlib.RingTheory.RingHom.PurelyInseparable
public import Mathlib.RingTheory.Etale.QuasiFinite
public import StacksFrontier.RingTheory.Etale.LocalStructure
public import StacksFrontier.RingTheory.Ideal.GoingUp
public import StacksFrontier.RingTheory.Etale.IndEtaleFibres
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
public import StacksFrontier.RingTheory.Unramified.LocalStructure
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Splitting an integral algebra after an étale extension

An integral algebra with only finitely many primes above a fixed prime and finite maximal
separable residue-field subextensions becomes, after an étale base change at that prime, a finite
product of integral algebras. Each factor has a unique prime above the chosen prime, and the
corresponding residue-field extension is purely inseparable.

## Main results

* `Algebra.exists_etale_completeOrthogonalIdempotents_integral_isPurelyInseparable`: the étale
  extension and the product decomposition.

The product decomposition is a complete family of orthogonal idempotents of the base-changed
algebra, whose factors are the localizations at those idempotents. The hypothesis on the maximal
separable subextension is finiteness of `separableClosure`.

## References

* [Stacks Project, Tag 0BSR](https://stacks.math.columbia.edu/tag/0BSR)
-/

@[expose] public section

open TensorProduct

universe u u₁ v w


namespace Algebra


private lemma maximal_fiber_prime
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) [q.IsPrime] : q.IsMaximal := by
  have : Algebra.IsIntegral p.ResidueField (p.Fiber S) := inferInstance
  exact Algebra.IsIntegral.isMaximal_of_isPrime (k := p.ResidueField) q

@[sga "3 V 4.1" "more general"]
private lemma primes_over_incomparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (p : Ideal R) [p.IsPrime]
    (q q' : p.primesOver S) (hne : q ≠ q') : ¬ (q : Ideal S) ≤ q' := by
  intro hle
  let F := PrimeSpectrum.primesOverOrderIsoFiber R S p
  have hmax : (F q).asIdeal.IsMaximal := maximal_fiber_prime p _
  have hle' : F q ≤ F q' := F.monotone hle
  have heq : F q = F q' := PrimeSpectrum.ext
    (hmax.eq_of_le (F q').isPrime.ne_top hle')
  exact hne (F.injective heq)

private lemma fiber_prime_comap
    {R : Type u} {T : Type v} {S : Type w}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra T S] [Algebra R S] [IsScalarTower R T S]
    (p : Ideal R) [p.IsPrime] (Q : PrimeSpectrum (p.Fiber S)) :
    let f : p.Fiber T →ₐ[p.ResidueField] p.Fiber S :=
      Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom R T S)
    (((PrimeSpectrum.primesOverOrderIsoFiber R T p).symm
      (PrimeSpectrum.comap f.toRingHom Q)) : Ideal T) =
      (((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm Q : p.primesOver S) : Ideal S).comap
        (algebraMap T S) := by
  intro f
  rw [PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply,
    PrimeSpectrum.coe_primesOverOrderIsoFiber_symm_apply]
  ext t
  simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  change f (Algebra.TensorProduct.includeRight t) ∈ Q.asIdeal ↔
    Algebra.TensorProduct.includeRight (algebraMap T S t) ∈ Q.asIdeal
  simp [f, Algebra.TensorProduct.map_tmul]

/-- The contraction of a prime lying over `p` along a tower `R → D → S` still lies over `p`. -/
private lemma liesOver_comap_algebraMap
    {R : Type u} {D : Type v} {S : Type w} [CommRing R] [CommRing D] [CommRing S]
    [Algebra R D] [Algebra D S] [Algebra R S] [IsScalarTower R D S]
    (p : Ideal R) (Q : Ideal S) [Q.LiesOver p] : (Q.comap (algebraMap D S)).LiesOver p :=
  have : Q.LiesOver (Q.comap (algebraMap D S)) := ⟨rfl⟩
  Ideal.LiesOver.tower_bot Q _ p



private lemma fiber_to_residue_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (p : Ideal R) [p.IsPrime] (q : p.primesOver S) :
    let P := PrimeSpectrum.primesOverOrderIsoFiber R S p q
    letI : (q : Ideal S).IsPrime := q.2.1
    letI : (q : Ideal S).LiesOver p := q.2.2
    letI := Localization.AtPrime.algebraOfLiesOver p (q : Ideal S)
    ∃ f : p.Fiber S →ₐ[p.ResidueField] (q : Ideal S).ResidueField,
      Function.Surjective f ∧ RingHom.ker f.toRingHom = P.asIdeal ∧
      ∀ s : S, f (Algebra.TensorProduct.includeRight s) =
        algebraMap S (q : Ideal S).ResidueField s := by
  classical
  let : (q : Ideal S).IsPrime := q.2.1
  let : (q : Ideal S).LiesOver p := q.2.2
  let := Localization.AtPrime.algebraOfLiesOver p (q : Ideal S)
  let P := PrimeSpectrum.primesOverOrderIsoFiber R S p q
  let φ₁ : p.ResidueField →ₐ[R] (q : Ideal S).ResidueField :=
    Ideal.ResidueField.mapₐ p (q : Ideal S) (Algebra.ofId R S)
      ((q : Ideal S).over_def p)
  let φ₂ : S →ₐ[R] (q : Ideal S).ResidueField :=
    IsScalarTower.toAlgHom R S (q : Ideal S).ResidueField
  let g : p.Fiber S →ₐ[R] (q : Ideal S).ResidueField :=
    Algebra.TensorProduct.lift φ₁ φ₂ (fun x y => mul_comm _ _)
  have hker : RingHom.ker g.toRingHom = P.asIdeal := rfl
  have hscalar (x : p.ResidueField) :
      g (algebraMap p.ResidueField (p.Fiber S) x) =
        algebraMap p.ResidueField (q : Ideal S).ResidueField x := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    change g (x ⊗ₜ[R] 1) = _
    change φ₁ x * φ₂ 1 = _
    simp only [map_one, mul_one]
    rfl
  let f : p.Fiber S →ₐ[p.ResidueField] (q : Ideal S).ResidueField :=
    { g.toRingHom with commutes' := hscalar }
  have hinc (s : S) : f (Algebra.TensorProduct.includeRight s) =
      algebraMap S (q : Ideal S).ResidueField s := by
    change g ((1 : p.ResidueField) ⊗ₜ[R] s) = _
    change φ₁ 1 * φ₂ s = _
    simp [φ₂, IsScalarTower.toAlgHom_apply]
  have hF : Function.Surjective f := by
    have hmax : P.asIdeal.IsMaximal := maximal_fiber_prime p P.asIdeal
    set T : Subring (q : Ideal S).ResidueField := f.toRingHom.range
    have hfield : IsField T :=
      MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
        ((Ideal.quotEquivOfEq hker.symm).trans
          (RingHom.quotientKerEquivRange f.toRingHom)).symm.toMulEquiv
    have hS (s : S) : algebraMap S (q : Ideal S).ResidueField s ∈ T :=
      ⟨Algebra.TensorProduct.includeRight s, hinc s⟩
    have hQ : ∀ x : S ⧸ (q : Ideal S),
        algebraMap (S ⧸ (q : Ideal S)) (q : Ideal S).ResidueField x ∈ T := by
      intro x
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.algebraMap_quotient_residueField_mk]
      exact hS s
    intro y
    obtain ⟨x, d, hd, hxd⟩ :=
      IsFractionRing.div_surjective (A := S ⧸ (q : Ideal S)) y
    have hdne : algebraMap (S ⧸ (q : Ideal S)) (q : Ideal S).ResidueField d ≠ 0 := by
      simp only [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      exact nonZeroDivisors.ne_zero hd
    have hyT : y ∈ T := by
      rw [← hxd, div_eq_mul_inv]
      exact T.mul_mem (hQ x) (Subring.inv_mem_of_isField hfield (hQ d) hdne)
    exact hyT
  exact ⟨f, hF, hker, hinc⟩

private lemma residueFieldEquiv_of_surjective_to_field
    {A : Type u} {K : Type v} [CommRing A] [Field K]
    (f : A →+* K) (hf : Function.Surjective f) :
    letI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    ∃ e : (RingHom.ker f).ResidueField ≃+* K,
      ∀ a : A, e (algebraMap A (RingHom.ker f).ResidueField a) = f a := by
  let : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  let : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  let e₀ : (A ⧸ RingHom.ker f) ≃+* (RingHom.ker f).ResidueField :=
    RingEquiv.ofBijective (algebraMap _ _)
      (RingHom.ker f).bijective_algebraMap_quotient_residueField
  let e : (RingHom.ker f).ResidueField ≃+* K :=
    e₀.symm.trans (f.quotientKerEquivOfSurjective hf)
  refine ⟨e, ?_⟩
  intro a
  change e (e₀ (Ideal.Quotient.mk _ a)) = f a
  simp [e, RingHom.quotientKerEquivOfSurjective_apply_mk]

private lemma purelyInseparable_of_equiv_square
    {F : Type u} {E : Type v} {F' : Type w} {E' : Type*}
    [Field F] [Field E] [Field F'] [Field E']
    (f : F →+* E) (g : F' →+* E')
    (eF : F ≃+* F') (eE : E ≃+* E')
    (hcomm : eE.toRingHom.comp f = g.comp eF.toRingHom)
    (hg : g.IsPurelyInseparable) : f.IsPurelyInseparable := by
  let : Algebra F E := f.toAlgebra
  let : Algebra F' E' := g.toAlgebra
  have hgp : IsPurelyInseparable F' E' := hg
  change IsPurelyInseparable F E
  let q := ringExpChar F'
  have : ExpChar F' q := ringExpChar.expChar F'
  have : ExpChar F q :=
    expChar_of_injective_ringHom (f := eF.symm.toRingHom) eF.symm.injective q
  have : ExpChar E q := expChar_of_injective_ringHom (f := f) f.injective q
  apply (isPurelyInseparable_iff_pow_mem F q).mpr
  intro x
  obtain ⟨n, y, hy⟩ := (isPurelyInseparable_iff_pow_mem F' q).mp hgp (eE x)
  refine ⟨n, eF.symm y, ?_⟩
  apply eE.injective
  calc
    eE (algebraMap F E (eF.symm y)) = g y := by
      change eE (f (eF.symm y)) = g y
      simpa using RingHom.congr_fun hcomm (eF.symm y)
    _ = (eE x) ^ q ^ n := hy
    _ = eE (x ^ q ^ n) := by simp

private lemma residueFieldEquiv_square
    {A : Type u} {B : Type v} {K : Type w} {L : Type*}
    [CommRing A] [CommRing B] [Field K] [Field L]
    (u : A →+* K) (v : B →+* L) (f : A →+* B) (g : K →+* L)
    (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hcomm : v.comp f = g.comp u)
    (hker : RingHom.ker u = (RingHom.ker v).comap f) :
    letI : (RingHom.ker u).IsPrime := RingHom.ker_isPrime u
    letI : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
    ∃ (eA : (RingHom.ker u).ResidueField ≃+* K)
      (eB : (RingHom.ker v).ResidueField ≃+* L),
      eB.toRingHom.comp
        (Ideal.ResidueField.map (RingHom.ker u) (RingHom.ker v) f hker) =
        g.comp eA.toRingHom := by
  let : (RingHom.ker u).IsPrime := RingHom.ker_isPrime u
  let : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
  have : (RingHom.ker u).IsMaximal := RingHom.ker_isMaximal_of_surjective u hu
  have : (RingHom.ker v).IsMaximal := RingHom.ker_isMaximal_of_surjective v hv
  obtain ⟨eA, heA⟩ := residueFieldEquiv_of_surjective_to_field u hu
  obtain ⟨eB, heB⟩ := residueFieldEquiv_of_surjective_to_field v hv
  let m : (RingHom.ker u).ResidueField →+* (RingHom.ker v).ResidueField :=
    Ideal.ResidueField.map (RingHom.ker u) (RingHom.ker v) f hker
  have hsquare : eB.toRingHom.comp m = g.comp eA.toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨a, rfl⟩ := (RingHom.ker u).algebraMap_residueField_surjective x
    simp only [RingHom.comp_apply]
    dsimp only [m]
    rw [Ideal.ResidueField.map_algebraMap]
    change eB (algebraMap B (RingHom.ker v).ResidueField (f a)) =
      g (eA (algebraMap A (RingHom.ker u).ResidueField a))
    rw [heA, heB]
    simpa only [RingHom.comp_apply] using (RingHom.congr_fun hcomm a)
  exact ⟨eA, eB, hsquare⟩

private lemma residue_purelyInseparable_of_surjective_field_square
    {A : Type u} {B : Type v} {K : Type w} {L : Type*}
    [CommRing A] [CommRing B] [Field K] [Field L]
    (u : A →+* K) (v : B →+* L) (f : A →+* B) (g : K →+* L)
    (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hcomm : v.comp f = g.comp u)
    (hker : RingHom.ker u = (RingHom.ker v).comap f)
    (hg : g.IsPurelyInseparable) :
    letI : (RingHom.ker u).IsPrime := RingHom.ker_isPrime u
    letI : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
    (Ideal.ResidueField.map (RingHom.ker u) (RingHom.ker v) f hker).IsPurelyInseparable := by
  let : (RingHom.ker u).IsPrime := RingHom.ker_isPrime u
  let : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
  obtain ⟨eA, eB, hsquare⟩ := residueFieldEquiv_square u v f g hu hv hcomm hker
  exact purelyInseparable_of_equiv_square _ g eA eB hsquare hg

private lemma residue_purelyInseparable_transport
    {A : Type u} {B : Type v} {K : Type w} {L : Type*}
    [CommRing A] [CommRing B] [Field K] [Field L]
    (f : A →+* B) (u : A →+* K) (v : B →+* L)
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (hP : RingHom.ker u = P) (hQ : RingHom.ker v = Q)
    (hker : RingHom.ker u = (RingHom.ker v).comap f)
    (hPQ : P = Q.comap f) :
    letI : (RingHom.ker u).IsPrime := RingHom.ker_isPrime u
    letI : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
    (Ideal.ResidueField.map (RingHom.ker u) (RingHom.ker v) f
        hker).IsPurelyInseparable ↔
      (Ideal.ResidueField.map P Q f hPQ).IsPurelyInseparable := by
  subst P
  subst Q
  rfl

private lemma purelyInseparable_of_surjective_field_square
    {A : Type u} {B : Type v} {K : Type w} {L : Type*}
    [CommRing A] [CommRing B] [Field K] [Field L]
    (u : A →+* K) (v : B →+* L) (f : A →+* B) (g : K →+* L)
    (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hcomm : v.comp f = g.comp u)
    (hker : RingHom.ker u = (RingHom.ker v).comap f)
    (hf : letI : (RingHom.ker u).IsPrime := RingHom.ker_isPrime u
      letI : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
      (Ideal.ResidueField.map (RingHom.ker u) (RingHom.ker v) f
        hker).IsPurelyInseparable) : g.IsPurelyInseparable := by
  let : (RingHom.ker u).IsPrime := RingHom.ker_isPrime u
  let : (RingHom.ker v).IsPrime := RingHom.ker_isPrime v
  obtain ⟨eA, eB, hsquare⟩ := residueFieldEquiv_square u v f g hu hv hcomm hker
  let m : (RingHom.ker u).ResidueField →+* (RingHom.ker v).ResidueField :=
    Ideal.ResidueField.map (RingHom.ker u) (RingHom.ker v) f hker
  refine purelyInseparable_of_equiv_square g m eA.symm eB.symm ?_ hf
  apply RingHom.ext
  intro x
  apply eB.injective
  change eB (eB.symm (g x)) = eB (m (eA.symm x))
  rw [eB.apply_symm_apply]
  have h := RingHom.congr_fun hsquare (eA.symm x)
  change eB (m (eA.symm x)) = g (eA (eA.symm x)) at h
  simpa using h.symm

private lemma integral_away_idempotent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (e : S) (he : IsIdempotentElem e) :
    Algebra.IsIntegral R (Localization.Away e) :=
  Algebra.IsIntegral.of_surjective
    (IsScalarTower.toAlgHom R S (Localization.Away e))
    (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he)

private lemma finite_adjoin_of_integral
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (t : Finset S) :
    Module.Finite R (Algebra.adjoin R (t : Set S)) :=
  Algebra.finite_adjoin_of_finite_of_isIntegral t.finite_toSet
    (fun x _ => Algebra.IsIntegral.isIntegral x)



private lemma fg_iSup_of_finite
    {R : Type u} {S : Type v} {ι : Type w} [CommRing R] [CommRing S]
    [Algebra R S] [Finite ι] (C : ι → Subalgebra R S)
    (hC : ∀ i, (C i).FG) : (⨆ i, C i).FG := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  choose t ht using hC
  let t' : Finset S := Finset.univ.biUnion t
  refine ⟨t', le_antisymm ?_ ?_⟩
  · apply Algebra.adjoin_le
    intro x hx
    obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.mp hx
    have hxi' : x ∈ C i := (ht i) ▸ Algebra.subset_adjoin hxi
    exact (le_iSup C i) hxi'
  · refine iSup_le fun i => ?_
    rw [← ht i]
    exact Algebra.adjoin_mono fun x hx => Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩


private lemma isPurelyInseparable_of_primitive_separableClosure_mem_range
    {K : Type u} {M : Type v} {E : Type w}
    [Field K] [Field M] [Field E] [Algebra K M] [Algebra M E]
    [Algebra K E] [IsScalarTower K M E] [Algebra.IsAlgebraic K E]
    (θ : separableClosure K E)
    (hθ : IntermediateField.adjoin K {θ} = ⊤)
    (hmem : (θ : E) ∈ Set.range (algebraMap M E)) :
    IsPurelyInseparable M E := by
  let φ : M →ₐ[K] E := IsScalarTower.toAlgHom K M E
  have hsep : separableClosure K E = IntermediateField.adjoin K {(θ : E)} := by
    have h := congrArg
      (fun L : IntermediateField K (separableClosure K E) => IntermediateField.lift L) hθ
    simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using h.symm
  have hle : separableClosure K E ≤ φ.fieldRange := by
    rw [hsep, IntermediateField.adjoin_simple_le_iff]
    exact hmem
  let e := ringExpChar K
  have : ExpChar K e := ringExpChar.expChar K
  have : ExpChar M e := expChar_of_injective_ringHom (algebraMap K M).injective e
  have : ExpChar (separableClosure K E) e :=
    expChar_of_injective_ringHom (algebraMap K (separableClosure K E)).injective e
  apply (isPurelyInseparable_iff_pow_mem M e).mpr
  intro x
  obtain ⟨n, y, hy⟩ := (isPurelyInseparable_iff_pow_mem (separableClosure K E) e).mp
    (separableClosure.isPurelyInseparable K E) x
  have hy' : (y : E) ∈ φ.fieldRange := hle y.property
  obtain ⟨z, hz⟩ := hy'
  have hy0 : (y : E) = x ^ e ^ n := hy
  exact ⟨n, z, by simpa [φ] using hz.trans hy0⟩

private lemma residue_algebraMap_eq_map
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] [J.LiesOver I]
    [Algebra (Localization.AtPrime I) (Localization.AtPrime J)]
    [IsScalarTower A (Localization.AtPrime I) (Localization.AtPrime J)] :
    (algebraMap I.ResidueField J.ResidueField) =
      Ideal.ResidueField.map I J (algebraMap A B) (J.over_def I) :=
  Ideal.ResidueField.ringHom_ext <| by
    ext x
    simp [← IsScalarTower.algebraMap_apply]

private lemma residue_tower_algebraMap
    {R : Type u} {T : Type v} {S : Type w}
    [CommRing R] [CommRing T] [CommRing S]
    [Algebra R T] [Algebra T S] [Algebra R S] [IsScalarTower R T S]
    (p : Ideal R) [p.IsPrime] (P : Ideal T) [P.IsPrime] [P.LiesOver p]
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P] [Q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P)]
    [Algebra (Localization.AtPrime P) (Localization.AtPrime Q)]
    [IsScalarTower T (Localization.AtPrime P) (Localization.AtPrime Q)]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime Q)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime Q)] :
    (algebraMap P.ResidueField Q.ResidueField).comp
      (algebraMap p.ResidueField P.ResidueField) =
      algebraMap p.ResidueField Q.ResidueField := by
  refine Ideal.ResidueField.ringHom_ext ?_
  ext x
  rw [RingHom.comp_apply, residue_algebraMap_eq_map p P,
    residue_algebraMap_eq_map P Q, residue_algebraMap_eq_map p Q]
  simp [IsScalarTower.algebraMap_apply R T S]

private lemma exists_fg_subalgebra_primitive_residue
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (hfinite : letI := Localization.AtPrime.algebraOfLiesOver p q
      Module.Finite p.ResidueField (separableClosure p.ResidueField q.ResidueField)) :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    ∃ C : Subalgebra R S, C.FG ∧
      ∃ θ : separableClosure p.ResidueField q.ResidueField,
        IntermediateField.adjoin p.ResidueField {θ} = ⊤ ∧
        ∃ a b : S, a ∈ C ∧ b ∈ C ∧
          (θ : q.ResidueField) =
            algebraMap S q.ResidueField a / algebraMap S q.ResidueField b := by
  classical
  let := Localization.AtPrime.algebraOfLiesOver p q
  let : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) := inferInstance
  let : Algebra.IsAlgebraic p.ResidueField q.ResidueField :=
    instIsAlgebraicResidueFieldOfIsIntegral p q
  let := hfinite
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element p.ResidueField
    (separableClosure p.ResidueField q.ResidueField)
  obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (A := S ⧸ q) (θ : q.ResidueField)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  let C : Subalgebra R S := Algebra.adjoin R ({a, b} : Finset S)
  refine ⟨C, Subalgebra.fg_adjoin_finset _, θ, hθ, a, b, ?_, ?_, ?_⟩
  · exact Algebra.subset_adjoin (by simp : a ∈ ({a, b} : Finset S))
  · exact Algebra.subset_adjoin (by simp : b ∈ ({a, b} : Finset S))
  · simpa using hab.symm

private noncomputable def fiber_baseChange_equiv
    {R : Type u} {R' : Type v} {X : Type w}
    [CommRing R] [CommRing R'] [CommRing X]
    [Algebra R R'] [Algebra R X]
    (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime]
    [p'.LiesOver p]
    [Algebra p.ResidueField p'.ResidueField]
    [IsScalarTower R p.ResidueField p'.ResidueField] :
    p'.ResidueField ⊗[p.ResidueField] (p.Fiber X) ≃ₐ[p'.ResidueField]
      p'.Fiber (R' ⊗[R] X) := by
  letI : Algebra X (R' ⊗[R] X) := Algebra.TensorProduct.rightAlgebra
  letI : Algebra.IsPushout R X R' (R' ⊗[R] X) := Algebra.IsPushout.symm inferInstance
  exact AlgEquiv.ofRingEquiv (f :=
    (Algebra.TensorProduct.cancelBaseChange R p.ResidueField p'.ResidueField
        p'.ResidueField X).toRingEquiv.trans
      ((Algebra.TensorProduct.comm R p'.ResidueField X).toRingEquiv.trans
        ((Algebra.IsPushout.cancelBaseChangeAlg R X R' (R' ⊗[R] X)
          p'.ResidueField).symm.toRingEquiv.trans
          (Algebra.TensorProduct.comm R' (R' ⊗[R] X) p'.ResidueField).toRingEquiv)))
    (fun x => by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.comm_tmul,
        Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul, Algebra.TensorProduct.one_def,
        Algebra.TensorProduct.cancelBaseChange_tmul])

private lemma fiber_baseChange_equiv_tmul_tmul
    {R : Type u} {R' : Type v} {X : Type w}
    [CommRing R] [CommRing R'] [CommRing X]
    [Algebra R R'] [Algebra R X]
    (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime]
    [p'.LiesOver p]
    [Algebra p.ResidueField p'.ResidueField]
    [IsScalarTower R p.ResidueField p'.ResidueField]
    (y : p'.ResidueField) (x : p.ResidueField) (s : X) :
    fiber_baseChange_equiv p p'
      (y ⊗ₜ[p.ResidueField] (x ⊗ₜ[R] s)) =
        (x • y) ⊗ₜ[R'] (1 ⊗ₜ[R] s : R' ⊗[R] X) := by
  let : Algebra X (R' ⊗[R] X) := Algebra.TensorProduct.rightAlgebra
  simp [fiber_baseChange_equiv, Algebra.TensorProduct.comm_tmul,
    Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul]
  rfl

/-- **The fibre-residue square of a tower.** For a tower `R → A → B` of integral algebras, a
prime `Q` of `B` lying over `p` and its contraction `P` to `A`, the fibre algebras `p.Fiber A`
and `p.Fiber B` surject onto the residue fields `κ(P)` and `κ(Q)`, with kernels the fibre primes
corresponding to `P` and `Q`, and the resulting square commutes. -/
private lemma fiber_residue_square
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
    (p : Ideal R) [p.IsPrime]
    (P : Ideal A) [P.IsPrime] [P.LiesOver p]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p]
    (hPQ : P = Q.comap (algebraMap A B)) :
    let fb : p.Fiber A →ₐ[p.ResidueField] p.Fiber B :=
      Algebra.TensorProduct.map (AlgHom.id _ _) (IsScalarTower.toAlgHom R A B)
    let PA : p.primesOver A := ⟨P, inferInstance, inferInstance⟩
    let QB : p.primesOver B := ⟨Q, inferInstance, inferInstance⟩
    ∃ (u : p.Fiber A →+* P.ResidueField) (v : p.Fiber B →+* Q.ResidueField),
      Function.Surjective u ∧ Function.Surjective v ∧
      RingHom.ker u = (PrimeSpectrum.primesOverOrderIsoFiber R A p PA).asIdeal ∧
      RingHom.ker v = (PrimeSpectrum.primesOverOrderIsoFiber R B p QB).asIdeal ∧
      (PrimeSpectrum.primesOverOrderIsoFiber R A p PA).asIdeal =
        (PrimeSpectrum.primesOverOrderIsoFiber R B p QB).asIdeal.comap fb.toRingHom ∧
      v.comp fb.toRingHom =
        (Ideal.ResidueField.map P Q (algebraMap A B) hPQ).comp u := by
  intro fb PA QB
  let FA := PrimeSpectrum.primesOverOrderIsoFiber R A p
  let FB := PrimeSpectrum.primesOverOrderIsoFiber R B p
  have hfiber : (FA PA).asIdeal = (FB QB).asIdeal.comap fb.toRingHom := by
    have h := fiber_prime_comap (R := R) (T := A) (S := B) p (FB QB)
    have hq : FB.symm (FB QB) = QB := FB.symm_apply_apply QB
    rw [hq] at h
    have hspec : FA PA = PrimeSpectrum.comap fb.toRingHom (FB QB) := by
      apply FA.symm.injective
      apply Subtype.ext
      simpa only [FA.symm_apply_apply] using hPQ.trans h.symm
    exact congrArg PrimeSpectrum.asIdeal hspec
  let : Q.LiesOver P := ⟨hPQ⟩
  let := Localization.AtPrime.algebraOfLiesOver p P
  let := Localization.AtPrime.algebraOfLiesOver P Q
  let := Localization.AtPrime.algebraOfLiesOver p Q
  let : IsScalarTower p.ResidueField P.ResidueField Q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (residue_tower_algebraMap p P Q).symm
  obtain ⟨u, hu, huk, hua⟩ := fiber_to_residue_surjective p PA
  obtain ⟨v, hv, hvk, hva⟩ := fiber_to_residue_surjective p QB
  refine ⟨u.toRingHom, v.toRingHom, hu, hv, huk, hvk, hfiber, ?_⟩
  have hg : (Ideal.ResidueField.map P Q (algebraMap A B) hPQ) =
      (algebraMap P.ResidueField Q.ResidueField) := (residue_algebraMap_eq_map P Q).symm
  rw [hg]
  refine Algebra.TensorProduct.ringHom_ext (RingHom.ext fun x => ?_) (RingHom.ext fun a => ?_)
  · change v (fb (algebraMap p.ResidueField (p.Fiber A) x)) =
      algebraMap P.ResidueField Q.ResidueField (u (algebraMap p.ResidueField (p.Fiber A) x))
    rw [fb.commutes, v.commutes, u.commutes, ← IsScalarTower.algebraMap_apply]
  · change v (fb ((1 : p.ResidueField) ⊗ₜ[R] a)) =
      algebraMap P.ResidueField Q.ResidueField (u ((1 : p.ResidueField) ⊗ₜ[R] a))
    have h2 : u ((1 : p.ResidueField) ⊗ₜ[R] a) = algebraMap A P.ResidueField a := hua a
    have h1 : v ((1 : p.ResidueField) ⊗ₜ[R] (algebraMap A B a)) =
        algebraMap B Q.ResidueField (algebraMap A B a) := hva _
    have hfbx : fb ((1 : p.ResidueField) ⊗ₜ[R] a) =
        (1 : p.ResidueField) ⊗ₜ[R] (algebraMap A B a) := by
      simp [fb, Algebra.TensorProduct.map_tmul]
    rw [hfbx, h1, h2, residue_algebraMap_eq_map P Q, Ideal.ResidueField.map_algebraMap]


/-- **Purely inseparable residue extensions pass from the fibre to the rings.** For a tower
`R → A → B` of integral algebras, if the fibre over `p` has purely inseparable residue field
extensions, then so has `A → B` at every prime of `B` over `p`. -/
private lemma residue_purelyInseparable_of_fiber
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
    (p : Ideal R) [p.IsPrime]
    (P : Ideal A) [P.IsPrime] [P.LiesOver p]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p]
    (hPQ : P = Q.comap (algebraMap A B))
    (hfib :
      let fb : p.Fiber A →ₐ[p.ResidueField] p.Fiber B :=
        Algebra.TensorProduct.map (AlgHom.id _ _) (IsScalarTower.toAlgHom R A B)
      ∀ (P' : Ideal (p.Fiber A)) [P'.IsPrime]
        (Q' : Ideal (p.Fiber B)) [Q'.IsPrime]
        (h : P' = Q'.comap fb.toRingHom),
        (Ideal.ResidueField.map P' Q' fb.toRingHom h).IsPurelyInseparable) :
    (Ideal.ResidueField.map P Q (algebraMap A B) hPQ).IsPurelyInseparable := by
  obtain ⟨u, v, hu, hv, huk, hvk, hfiber, hsquare⟩ := fiber_residue_square p P Q hPQ
  set fb : p.Fiber A →ₐ[p.ResidueField] p.Fiber B :=
    Algebra.TensorProduct.map (AlgHom.id _ _) (IsScalarTower.toAlgHom R A B) with hfbdef
  have hker : RingHom.ker u =
      (RingHom.ker v).comap fb.toRingHom := by
    rw [huk, hvk]; exact hfiber
  let : (RingHom.ker u).IsPrime := RingHom.ker_isPrime _
  let : (RingHom.ker v).IsPrime := RingHom.ker_isPrime _
  have hfib' :
      (Ideal.ResidueField.map (RingHom.ker u)
        (RingHom.ker v) fb.toRingHom hker).IsPurelyInseparable :=
    (residue_purelyInseparable_transport fb.toRingHom u v _ _
      huk hvk hker hfiber).2 (hfib _ _ hfiber)
  exact purelyInseparable_of_surjective_field_square u v fb.toRingHom
    (Ideal.ResidueField.map P Q (algebraMap A B) hPQ) hu hv hsquare hker hfib'

/-- **Purely inseparable residue extensions pass from the rings to the fibre.** For a tower
`R → A → B` of integral algebras, if `A → B` has purely inseparable residue field extensions at
every prime of `B` over `p`, then so has the fibre over `p`. -/
private lemma fiber_purelyInseparable_of_residue
    {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
    (p : Ideal R) [p.IsPrime]
    (hring : ∀ (P : Ideal A) [P.IsPrime] [P.LiesOver p] (Q : Ideal B) [Q.IsPrime]
      [Q.LiesOver p] (hPQ : P = Q.comap (algebraMap A B)),
      (Ideal.ResidueField.map P Q (algebraMap A B) hPQ).IsPurelyInseparable) :
    let fb : p.Fiber A →ₐ[p.ResidueField] p.Fiber B :=
      Algebra.TensorProduct.map (AlgHom.id _ _) (IsScalarTower.toAlgHom R A B)
    ∀ (P' : Ideal (p.Fiber A)) [P'.IsPrime]
      (Q' : Ideal (p.Fiber B)) [Q'.IsPrime]
      (h : P' = Q'.comap fb.toRingHom),
      (Ideal.ResidueField.map P' Q' fb.toRingHom h).IsPurelyInseparable := by
  intro fb P' _ Q' _ h
  let FA := PrimeSpectrum.primesOverOrderIsoFiber R A p
  let FB := PrimeSpectrum.primesOverOrderIsoFiber R B p
  let QS : PrimeSpectrum (p.Fiber B) := ⟨Q', inferInstance⟩
  let qb : p.primesOver B := FB.symm QS
  let : (qb : Ideal B).IsPrime := qb.2.1
  let : (qb : Ideal B).LiesOver p := qb.2.2
  set Q : Ideal B := (qb : Ideal B) with hQdef
  set P : Ideal A := Q.comap (algebraMap A B) with hPdef
  let : P.IsPrime := Ideal.comap_isPrime _ _
  let : Q.LiesOver P := ⟨rfl⟩
  let : P.LiesOver p := Ideal.LiesOver.tower_bot Q P p
  have hQB : (FB ⟨Q, inferInstance, inferInstance⟩).asIdeal = Q' := by
    have : FB ⟨Q, inferInstance, inferInstance⟩ = QS := by
      have := FB.apply_symm_apply QS
      exact this
    rw [this]
  obtain ⟨u, v, hu, hv, huk, hvk, hfiber, hsquare⟩ :=
    fiber_residue_square p P Q (rfl : P = Q.comap (algebraMap A B))
  have hker : RingHom.ker u =
      (RingHom.ker v).comap fb.toRingHom := by
    rw [huk, hvk]; exact hfiber
  let : (RingHom.ker u).IsPrime := RingHom.ker_isPrime _
  let : (RingHom.ker v).IsPrime := RingHom.ker_isPrime _
  have hbase := residue_purelyInseparable_of_surjective_field_square u v
    fb.toRingHom (Ideal.ResidueField.map P Q (algebraMap A B) rfl) hu hv hsquare hker
    (hring P Q rfl)
  have hkerP : RingHom.ker u = P' := by rw [huk, hfiber, hQB, h]
  have hkerQ : RingHom.ker v = Q' := hvk.trans hQB
  exact (residue_purelyInseparable_transport fb.toRingHom u v
    P' Q' hkerP hkerQ hker h).1 hbase


private lemma completeOrthogonalIdempotents_merge_last
    {A : Type*} [CommRing A] {n : ℕ} (e : Fin (n + 1) → A)
    (he : CompleteOrthogonalIdempotents e) (hn : 0 < n) :
    CompleteOrthogonalIdempotents
      (fun i : Fin n =>
        if i = ⟨0, hn⟩ then e i.castSucc + e (Fin.last n) else e i.castSucc) := by
  classical
  let i₀ : Fin n := ⟨0, hn⟩
  rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
  constructor
  · intro i j hij
    change (if i = i₀ then e i.castSucc + e (Fin.last n) else e i.castSucc) *
      (if j = i₀ then e j.castSucc + e (Fin.last n) else e j.castSucc) = 0
    split_ifs with hi hj
    · exact (hij (hi.trans hj.symm)).elim
    · subst i
      rw [add_mul, he.ortho (fun h => hj ((Fin.castSucc_injective n) h).symm),
        he.ortho (Fin.castSucc_ne_last j).symm, zero_add]
    · subst j
      rw [mul_add, he.ortho (fun h => hij ((Fin.castSucc_injective n) h)),
        he.ortho (Fin.castSucc_ne_last i), add_zero]
    · exact he.ortho (fun h => hij ((Fin.castSucc_injective n) h))
  · have hsum : (∑ i : Fin n,
          if i = i₀ then e i.castSucc + e (Fin.last n) else e i.castSucc) =
        (∑ i : Fin n, e i.castSucc) + e (Fin.last n) := by
      calc
        (∑ i : Fin n,
            if i = i₀ then e i.castSucc + e (Fin.last n) else e i.castSucc) =
          ∑ i : Fin n, (e i.castSucc +
            (if i = i₀ then e (Fin.last n) else 0)) := by
              apply Finset.sum_congr rfl
              intro i _
              split_ifs <;> simp
        _ = (∑ i : Fin n, e i.castSucc) + e (Fin.last n) := by
          rw [Finset.sum_add_distrib]
          simp
    rw [hsum]
    simpa only [Fin.sum_univ_castSucc] using he.complete

private lemma isPurelyInseparable_residueField_of_primitive_mem
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (p : Ideal R) [p.IsPrime]
    (D : Type v) [CommRing D] [Algebra R D] [Algebra D S] [IsScalarTower R D S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (θ : letI := Localization.AtPrime.algebraOfLiesOver p q
      separableClosure p.ResidueField q.ResidueField)
    (hθ : letI := Localization.AtPrime.algebraOfLiesOver p q
      IntermediateField.adjoin p.ResidueField {θ} = ⊤)
    (a b : D)
    (hab : letI := Localization.AtPrime.algebraOfLiesOver p q
      (θ : q.ResidueField) = algebraMap S q.ResidueField (algebraMap D S a) /
        algebraMap S q.ResidueField (algebraMap D S b)) :
    letI : (q.comap (algebraMap D S)).IsPrime := Ideal.comap_isPrime _ _
    (Ideal.ResidueField.map (q.comap (algebraMap D S)) q (algebraMap D S)
      rfl).IsPurelyInseparable := by
  let : (q.comap (algebraMap D S)).IsPrime := Ideal.comap_isPrime _ _
  set P : Ideal D := q.comap (algebraMap D S) with hPdef
  let : q.LiesOver P := ⟨rfl⟩
  let : P.LiesOver p := liesOver_comap_algebraMap p q
  let := Localization.AtPrime.algebraOfLiesOver p P
  let := Localization.AtPrime.algebraOfLiesOver P q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let : IsScalarTower p.ResidueField P.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (residue_tower_algebraMap p P q).symm
  have hmap (x : D) :
      algebraMap P.ResidueField q.ResidueField (algebraMap D P.ResidueField x) =
        algebraMap S q.ResidueField (algebraMap D S x) := by
    rw [residue_algebraMap_eq_map P q, Ideal.ResidueField.map_algebraMap]
  rw [show (Ideal.ResidueField.map P q (algebraMap D S) rfl) =
    (algebraMap P.ResidueField q.ResidueField) from (residue_algebraMap_eq_map P q).symm]
  refine RingHom.isPurelyInseparable_algebraMap_iff.2 ?_
  apply isPurelyInseparable_of_primitive_separableClosure_mem_range θ hθ
  refine ⟨algebraMap D P.ResidueField a / algebraMap D P.ResidueField b, ?_⟩
  rw [map_div₀, hmap, hmap]
  exact hab.symm

/-- **A module-finite subalgebra carrying the primes and the separable residue extensions.**
For an integral `R`-algebra `S` with finitely many primes over `p` whose residue extensions have
finite maximal separable subextensions, there is an intermediate algebra `R → D → S` with `D`
module-finite over `R` such that contraction to `D` is injective on the primes over `p` and every
residue extension `κ(Q ∩ D) ⊆ κ(Q)` is purely inseparable. -/
private lemma exists_moduleFinite_tower_residue_isPurelyInseparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (p : Ideal R) [p.IsPrime]
    (hfinite : Set.Finite {q : Ideal S | q.IsPrime ∧ q.LiesOver p})
    (hseparable : ∀ (q : Ideal S) (hq : q.IsPrime) (hqover : q.LiesOver p),
      letI := hq
      letI := hqover
      letI := Localization.AtPrime.algebraOfLiesOver p q
      Module.Finite p.ResidueField
        (separableClosure p.ResidueField q.ResidueField)) :
    ∃ (D : Type v) (_ : CommRing D) (_ : Algebra R D) (_ : Algebra D S)
      (_ : IsScalarTower R D S),
      Module.Finite R D ∧ Function.Injective (algebraMap D S) ∧
      Function.Injective
        (fun q : p.primesOver S => (q : Ideal S).comap (algebraMap D S)) ∧
      ∀ (q : Ideal S) (hq : q.IsPrime) (hqover : q.LiesOver p),
        letI := hq
        letI := hqover
        letI : (q.comap (algebraMap D S)).IsPrime := Ideal.comap_isPrime _ _
        (Ideal.ResidueField.map (q.comap (algebraMap D S)) q (algebraMap D S)
          rfl).IsPurelyInseparable := by
  classical
  let : Finite (p.primesOver S) := hfinite.to_subtype
  let : Fintype (p.primesOver S) := Fintype.ofFinite _
  have hdata (q : p.primesOver S) :
      let : (q : Ideal S).IsPrime := q.2.1
      let : (q : Ideal S).LiesOver p := q.2.2
      let := Localization.AtPrime.algebraOfLiesOver p (q : Ideal S)
      ∃ C : Subalgebra R S, C.FG ∧
        ∃ θ : separableClosure p.ResidueField (q : Ideal S).ResidueField,
          IntermediateField.adjoin p.ResidueField {θ} = ⊤ ∧
          ∃ a b : S, a ∈ C ∧ b ∈ C ∧
            (θ : (q : Ideal S).ResidueField) =
              algebraMap S (q : Ideal S).ResidueField a /
                algebraMap S (q : Ideal S).ResidueField b := by
    let : (q : Ideal S).IsPrime := q.2.1
    let : (q : Ideal S).LiesOver p := q.2.2
    exact exists_fg_subalgebra_primitive_residue p (q : Ideal S)
      (hseparable (q : Ideal S) q.2.1 q.2.2)
  let C : p.primesOver S → Subalgebra R S := fun q => (hdata q).choose
  have hC : ∀ q, (C q).FG := fun q => (hdata q).choose_spec.1
  let C₀ : Subalgebra R S := ⨆ q, C q
  have hC₀ : C₀.FG := fg_iSup_of_finite C hC
  let sep (q q' : p.primesOver S) : S :=
    if h : q = q' then 0 else
      Classical.choose (IsConcreteLE.not_le_iff_exists.mp
        (primes_over_incomparable p q q' h))
  let tSep : Finset S := (Finset.univ.product Finset.univ).image
    (fun ij : p.primesOver S × p.primesOver S => sep ij.1 ij.2)
  let D : Subalgebra R S := C₀ ⊔ Algebra.adjoin R (tSep : Set S)
  have hDfg : D.FG := hC₀.sup (Subalgebra.fg_adjoin_finset tSep)
  obtain ⟨t, ht⟩ := hDfg
  have hDfinite : Module.Finite R D := by
    rw [← ht]
    exact finite_adjoin_of_integral t
  have hsep_mem (q q' : p.primesOver S) (hne : q ≠ q') :
      sep q q' ∈ (q : Ideal S) ∧ sep q q' ∉ (q' : Ideal S) := by
    simpa [sep, hne] using Classical.choose_spec
      (IsConcreteLE.not_le_iff_exists.mp (primes_over_incomparable p q q' hne))
  have hsepD (q q' : p.primesOver S) : sep q q' ∈ D := by
    have hs : sep q q' ∈ tSep := Finset.mem_image.mpr
      ⟨(q, q'), Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩
    exact (le_sup_right : Algebra.adjoin R (tSep : Set S) ≤ D)
      (Algebra.subset_adjoin hs)
  let : Algebra D S := D.val.toAlgebra
  have : IsScalarTower R D S := IsScalarTower.of_algebraMap_eq' rfl
  have hinjD : Function.Injective (algebraMap D S) := Subtype.val_injective
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, hDfinite, hinjD, ?_, ?_⟩
  · intro q q' heq
    by_contra hne
    obtain ⟨hxq, hxq'⟩ := hsep_mem q q' hne
    have hxD : (⟨sep q q', hsepD q q'⟩ : D) ∈
        (q : Ideal S).comap (algebraMap D S) := hxq
    change (q : Ideal S).comap (algebraMap D S) =
      (q' : Ideal S).comap (algebraMap D S) at heq
    rw [heq] at hxD
    exact hxq' hxD
  · intro q hq hqover
    let := hq
    let := hqover
    obtain ⟨θ, hθ, a, b, ha, hb, hab⟩ :=
      (hdata (⟨q, hq, hqover⟩ : p.primesOver S)).choose_spec.2
    have hCD : C (⟨q, hq, hqover⟩ : p.primesOver S) ≤ D := (le_iSup C _).trans le_sup_left
    exact isPurelyInseparable_residueField_of_primitive_mem p D q θ hθ
      ⟨a, hCD ha⟩ ⟨b, hCD hb⟩ hab


/-- **Bijectivity on fibres from injectivity on primes.** For an injective integral extension
`D → S` of `R`-algebras, if contraction to `D` is injective on the primes of `S` lying over `p`,
then the induced map of fibre spectra over `p` is bijective. -/
private lemma fiber_comap_bijective_of_primesOver_comap_injective
    {R : Type u} {D : Type w} {S : Type v} [CommRing R] [CommRing D] [CommRing S]
    [Algebra R D] [Algebra D S] [Algebra R S] [IsScalarTower R D S]
    [Algebra.IsIntegral R D] [Algebra.IsIntegral R S]
    (p : Ideal R) [p.IsPrime]
    (hinj : Function.Injective (algebraMap D S))
    (hcomap : Function.Injective
      (fun q : p.primesOver S => (q : Ideal S).comap (algebraMap D S))) :
    Function.Bijective (PrimeSpectrum.comap
      (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom R D S) :
        p.Fiber D →ₐ[p.ResidueField] p.Fiber S).toRingHom) := by
  set fb : p.Fiber D →ₐ[p.ResidueField] p.Fiber S :=
    Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
      (IsScalarTower.toAlgHom R D S) with hfbdef
  have : Algebra.IsIntegral D S := Algebra.IsIntegral.tower_top R
  let : FaithfulSMul D S := (faithfulSMul_iff_algebraMap_injective D S).mpr hinj
  let pull : p.primesOver S → p.primesOver D := fun q => by
    let : (q : Ideal S).IsPrime := q.2.1
    let : (q : Ideal S).LiesOver p := q.2.2
    exact ⟨(q : Ideal S).comap (algebraMap D S), inferInstance, liesOver_comap_algebraMap p _⟩
  have hpull_inj : Function.Injective pull := fun q q' hqq' =>
    hcomap (congrArg Subtype.val hqq')
  have hpull_surj : Function.Surjective pull := by
    intro qD
    let : (qD : Ideal D).IsPrime := qD.2.1
    let : (qD : Ideal D).LiesOver p := qD.2.2
    have hker : RingHom.ker (algebraMap D S) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp hinj
    have hle : (⊥ : Ideal S).comap (algebraMap D S) ≤ (qD : Ideal D) := by
      rw [← RingHom.ker_eq_comap_bot, hker]
      exact bot_le
    obtain ⟨qS, -, hqSp, hqSeq⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (qD : Ideal D) ⊥ hle
    let : (qS : Ideal S).LiesOver (qD : Ideal D) := ⟨hqSeq.symm⟩
    have hqSR : qS.LiesOver p := .trans _ (qD : Ideal D) _
    exact ⟨⟨qS, hqSp, hqSR⟩, Subtype.ext hqSeq⟩
  let FD := PrimeSpectrum.primesOverOrderIsoFiber R D p
  let FS := PrimeSpectrum.primesOverOrderIsoFiber R S p
  have hfb_pull (Q : PrimeSpectrum (p.Fiber S)) :
      FD.symm (PrimeSpectrum.comap fb.toRingHom Q) = pull (FS.symm Q) :=
    Subtype.ext (fiber_prime_comap p Q)
  constructor
  · intro Q Q' h
    apply FS.symm.injective
    apply hpull_inj
    rw [← hfb_pull, ← hfb_pull, h]
  · intro Q
    obtain ⟨q, hq⟩ := hpull_surj (FD.symm Q)
    refine ⟨FS q, FD.symm.injective ?_⟩
    rw [hfb_pull, FS.symm_apply_apply]
    exact hq


/-- The canonical map from the fibre of `X` over `p` to the fibre of `R₁ ⊗[R] X` over a prime
`p₁` of `R₁` lying over `p`. -/
private noncomputable def fiberBaseChangeHom
    {R : Type u} {R₁ : Type u₁} (X : Type w)
    [CommRing R] [CommRing R₁] [CommRing X] [Algebra R R₁] [Algebra R X]
    (p : Ideal R) [p.IsPrime] (p₁ : Ideal R₁) [p₁.IsPrime] [p₁.LiesOver p]
    [Algebra p.ResidueField p₁.ResidueField]
    [IsScalarTower R p.ResidueField p₁.ResidueField] :
    p.Fiber X →+* p₁.Fiber (R₁ ⊗[R] X) :=
  (fiber_baseChange_equiv (X := X) p p₁).toRingHom.comp
    (Algebra.TensorProduct.includeRight :
      p.Fiber X →ₐ[p.ResidueField]
        p₁.ResidueField ⊗[p.ResidueField] (p.Fiber X)).toRingHom

/-- `fiberBaseChangeHom` is compatible with the structure maps from `κ(p)`: scalars from `κ(p)`
reach the fibre of `R₁ ⊗[R] X` over `p₁` equally through `p.Fiber X` and through `κ(p₁)`. -/
private lemma fiberBaseChangeHom_comp_algebraMap
    {R : Type u} {R₁ : Type u₁} (X : Type w)
    [CommRing R] [CommRing R₁] [CommRing X] [Algebra R R₁] [Algebra R X]
    (p : Ideal R) [p.IsPrime] (p₁ : Ideal R₁) [p₁.IsPrime] [p₁.LiesOver p]
    [Algebra p.ResidueField p₁.ResidueField]
    [IsScalarTower R p.ResidueField p₁.ResidueField] :
    (fiberBaseChangeHom X p p₁).comp (algebraMap p.ResidueField (p.Fiber X)) =
      (algebraMap p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] X))).comp
        (algebraMap p.ResidueField p₁.ResidueField) := by
  apply RingHom.ext
  intro x
  change fiber_baseChange_equiv (X := X) p p₁
      (1 ⊗ₜ[p.ResidueField] (algebraMap p.ResidueField (p.Fiber X) x)) =
    algebraMap p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] X))
      (algebraMap p.ResidueField p₁.ResidueField x)
  rw [← (fiber_baseChange_equiv (X := X) p p₁).commutes
    (algebraMap p.ResidueField p₁.ResidueField x)]
  congr 1
  calc
    (1 : p₁.ResidueField) ⊗ₜ[p.ResidueField]
        (algebraMap p.ResidueField (p.Fiber X) x) =
        (1 : p₁.ResidueField) ⊗ₜ[p.ResidueField]
          (x • (1 : p.Fiber X)) := by rw [Algebra.algebraMap_eq_smul_one]
    _ = (x • (1 : p₁.ResidueField)) ⊗ₜ[p.ResidueField]
        (1 : p.Fiber X) := TensorProduct.tmul_smul x _ _
    _ = (algebraMap p.ResidueField p₁.ResidueField x) ⊗ₜ[p.ResidueField]
        (1 : p.Fiber X) := by rw [Algebra.algebraMap_eq_smul_one]

/-- The fibre of `R₁ ⊗[R] X` over `p₁` is the base change of the fibre of `X` over `p` along
`κ(p) → κ(p₁)`. -/
private lemma isPushout_fiberBaseChangeHom
    {R : Type u} {R₁ : Type u₁} (X : Type w)
    [CommRing R] [CommRing R₁] [CommRing X] [Algebra R R₁] [Algebra R X]
    (p : Ideal R) [p.IsPrime] (p₁ : Ideal R₁) [p₁.IsPrime] [p₁.LiesOver p]
    [Algebra p.ResidueField p₁.ResidueField]
    [IsScalarTower R p.ResidueField p₁.ResidueField] :
    letI : Algebra (p.Fiber X) (p₁.Fiber (R₁ ⊗[R] X)) :=
      (fiberBaseChangeHom X p p₁).toAlgebra
    letI : Algebra p.ResidueField (p₁.Fiber (R₁ ⊗[R] X)) :=
      Algebra.compHom _ (algebraMap p.ResidueField p₁.ResidueField)
    letI : SMul p.ResidueField (p.Fiber X) :=
      (inferInstance : Algebra p.ResidueField (p.Fiber X)).toSMul
    letI : SMul p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] X)) :=
      (inferInstance : Algebra p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] X))).toSMul
    letI : SMul p.ResidueField (p₁.Fiber (R₁ ⊗[R] X)) :=
      (inferInstance : Algebra p.ResidueField (p₁.Fiber (R₁ ⊗[R] X))).toSMul
    letI : IsScalarTower p.ResidueField p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] X)) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    letI : IsScalarTower p.ResidueField (p.Fiber X) (p₁.Fiber (R₁ ⊗[R] X)) :=
      IsScalarTower.of_algebraMap_eq' (fiberBaseChangeHom_comp_algebraMap X p p₁).symm
    Algebra.IsPushout p.ResidueField p₁.ResidueField (p.Fiber X)
      (p₁.Fiber (R₁ ⊗[R] X)) := by
  let : Algebra (p.Fiber X) (p₁.Fiber (R₁ ⊗[R] X)) := (fiberBaseChangeHom X p p₁).toAlgebra
  let : Algebra p.ResidueField (p₁.Fiber (R₁ ⊗[R] X)) :=
    Algebra.compHom _ (algebraMap p.ResidueField p₁.ResidueField)
  let : SMul p.ResidueField (p.Fiber X) :=
    (inferInstance : Algebra p.ResidueField (p.Fiber X)).toSMul
  let : SMul p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] X)) :=
    (inferInstance : Algebra p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] X))).toSMul
  let : SMul p.ResidueField (p₁.Fiber (R₁ ⊗[R] X)) :=
    (inferInstance : Algebra p.ResidueField (p₁.Fiber (R₁ ⊗[R] X))).toSMul
  let : IsScalarTower p.ResidueField p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] X)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower p.ResidueField (p.Fiber X) (p₁.Fiber (R₁ ⊗[R] X)) :=
    IsScalarTower.of_algebraMap_eq' (fiberBaseChangeHom_comp_algebraMap X p p₁).symm
  let : Algebra (p.Fiber X) (p₁.ResidueField ⊗[p.ResidueField] (p.Fiber X)) :=
    Algebra.TensorProduct.rightAlgebra
  let E := fiber_baseChange_equiv (X := X) p p₁
  refine Algebra.IsPushout.of_equiv
    (S' := p₁.ResidueField ⊗[p.ResidueField] (p.Fiber X))
    { toFun := E
      invFun := E.symm
      left_inv := E.left_inv
      right_inv := E.right_inv
      map_mul' := E.map_mul
      map_add' := E.map_add
      commutes' := E.commutes } rfl

/-- Base change to `p₁` commutes with an `R`-algebra map `A → B` on the fibres over `p`. -/
private lemma fiberBaseChangeHom_comm
    {R : Type u} {R₁ : Type u₁} {A : Type v} {B : Type w}
    [CommRing R] [CommRing R₁] [CommRing A] [CommRing B]
    [Algebra R R₁] [Algebra R A] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (p₁ : Ideal R₁) [p₁.IsPrime] [p₁.LiesOver p]
    [Algebra p.ResidueField p₁.ResidueField]
    [IsScalarTower R p.ResidueField p₁.ResidueField]
    (φ : A →ₐ[R] B) :
    (Algebra.TensorProduct.map (AlgHom.id p₁.ResidueField p₁.ResidueField)
        (Algebra.TensorProduct.map (AlgHom.id R₁ R₁) φ)).toRingHom.comp
        (fiberBaseChangeHom A p p₁) =
      (fiberBaseChangeHom B p p₁).comp
        (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField) φ).toRingHom := by
  apply RingHom.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul x a =>
      change (Algebra.TensorProduct.map (AlgHom.id p₁.ResidueField p₁.ResidueField)
          (Algebra.TensorProduct.map (AlgHom.id R₁ R₁) φ))
          (fiber_baseChange_equiv (X := A) p p₁ (1 ⊗ₜ[p.ResidueField] (x ⊗ₜ[R] a))) =
        fiber_baseChange_equiv (X := B) p p₁ (1 ⊗ₜ[p.ResidueField]
          ((Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField) φ)
            (x ⊗ₜ[R] a)))
      rw [fiber_baseChange_equiv_tmul_tmul,
        show (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField) φ)
            (x ⊗ₜ[R] a) = x ⊗ₜ[R] (φ a) by simp [Algebra.TensorProduct.map_tmul],
        fiber_baseChange_equiv_tmul_tmul]
      simp [Algebra.TensorProduct.map_tmul]
  | add a b ha hb =>
      simpa only [map_add] using congrArg₂ (· + ·) ha hb


/-- **One factor of the decomposition.** Let `R₁ → A → B` be integral, `ρ` a prime of `A` over
`p₁` with purely inseparable residue extension, `r` a prime of `B` contracting to `ρ`, and `e` an
element of `B` outside `r` such that `r` is the only prime of `B` over `p₁` avoiding `e`. If the
fibre of `A → B` over `p₁` has purely inseparable residue extensions, then `B[1/e]` has exactly
one prime over `p₁`, and its residue extension over `κ(p₁)` is purely inseparable. -/
private lemma primesOver_away_eq_singleton_and_isPurelyInseparable
    {R₁ : Type u₁} {A : Type v} {B : Type w}
    [CommRing R₁] [CommRing A] [CommRing B]
    [Algebra R₁ A] [Algebra A B] [Algebra R₁ B] [IsScalarTower R₁ A B]
    [Algebra.IsIntegral R₁ A] [Algebra.IsIntegral R₁ B]
    (p₁ : Ideal R₁) [p₁.IsPrime]
    (ρ : Ideal A) [ρ.IsPrime] [ρ.LiesOver p₁]
    (r : Ideal B) [r.IsPrime] [r.LiesOver p₁]
    (hcomap : ρ = r.comap (algebraMap A B))
    (hρpure : let _ := Localization.AtPrime.algebraOfLiesOver p₁ ρ
      IsPurelyInseparable p₁.ResidueField ρ.ResidueField)
    (hfib :
      let fb : p₁.Fiber A →ₐ[p₁.ResidueField] p₁.Fiber B :=
        Algebra.TensorProduct.map (AlgHom.id _ _) (IsScalarTower.toAlgHom R₁ A B)
      ∀ (P' : Ideal (p₁.Fiber A)) [P'.IsPrime]
        (Q' : Ideal (p₁.Fiber B)) [Q'.IsPrime]
        (h : P' = Q'.comap fb.toRingHom),
        (Ideal.ResidueField.map P' Q' fb.toRingHom h).IsPurelyInseparable)
    (e : B) (hnot : e ∉ r)
    (huniq : ∀ Q : Ideal B, Q.IsPrime → Q.LiesOver p₁ → e ∉ Q → Q = r) :
    p₁.primesOver (Localization.Away e) =
        {r.map (algebraMap B (Localization.Away e))} ∧
      ∀ (q : Ideal (Localization.Away e)) (hq : q.IsPrime) (hqo : q.LiesOver p₁),
        let _ := hq
        let _ := hqo
        let _ := Localization.AtPrime.algebraOfLiesOver p₁ q
        IsPurelyInseparable p₁.ResidueField q.ResidueField := by
  have hdisj : Disjoint (Submonoid.powers e : Set B) (r : Set B) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime e).2 hnot
  have hsingle : p₁.primesOver (Localization.Away e) =
      {r.map (algebraMap B (Localization.Away e))} :=
    primesOver_eq_singleton_of_isLocalization (Submonoid.powers e) p₁ r hdisj
      fun Q hQ hQo hd => huniq Q hQ hQo ((Ideal.disjoint_powers_iff_notMem_of_isPrime e).1 hd)
  refine ⟨hsingle, ?_⟩
  intro q hq hqo
  let _ := hq
  let _ := hqo
  have hqeq : q = r.map (algebraMap B (Localization.Away e)) := by
    have hmem : q ∈ p₁.primesOver (Localization.Away e) := ⟨hq, hqo⟩
    rwa [hsingle] at hmem
  subst hqeq
  set r' : Ideal (Localization.Away e) := r.map (algebraMap B (Localization.Away e))
    with hr'def
  have hφpure : (Ideal.ResidueField.map ρ r (algebraMap A B) hcomap).IsPurelyInseparable :=
    residue_purelyInseparable_of_fiber p₁ ρ r hcomap hfib
  have hcomapr : r = r'.comap (algebraMap B (Localization.Away e)) :=
    (IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers e)
      (Localization.Away e) ‹r.IsPrime› hdisj).symm
  let _ : r.LiesOver ρ := ⟨hcomap⟩
  let _ : r'.LiesOver r := ⟨hcomapr⟩
  let _ := Localization.AtPrime.algebraOfLiesOver p₁ ρ
  let _ := Localization.AtPrime.algebraOfLiesOver ρ r
  let _ := Localization.AtPrime.algebraOfLiesOver p₁ r
  let _ := Localization.AtPrime.algebraOfLiesOver r r'
  let _ := Localization.AtPrime.algebraOfLiesOver p₁ r'
  let _ : IsScalarTower p₁.ResidueField ρ.ResidueField r.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (residue_tower_algebraMap p₁ ρ r).symm
  let _ : IsScalarTower p₁.ResidueField r.ResidueField r'.ResidueField :=
    IsScalarTower.of_algebraMap_eq' (residue_tower_algebraMap p₁ r r').symm
  have hpure₁ : IsPurelyInseparable ρ.ResidueField r.ResidueField := by
    rw [← RingHom.isPurelyInseparable_algebraMap_iff, residue_algebraMap_eq_map ρ r]
    exact hφpure
  let _ : IsPurelyInseparable p₁.ResidueField ρ.ResidueField := hρpure
  let _ : IsPurelyInseparable ρ.ResidueField r.ResidueField := hpure₁
  have hpure₂ : IsPurelyInseparable p₁.ResidueField r.ResidueField :=
    IsPurelyInseparable.trans p₁.ResidueField ρ.ResidueField r.ResidueField
  have hbij : Function.Bijective
      (Ideal.ResidueField.map r r' (algebraMap B (Localization.Away e)) hcomapr) :=
    (RingHom.surjectiveOnStalks_of_isLocalization
      (Submonoid.powers e) (Localization.Away e)).residueFieldMap_bijective r r' hcomapr
  have hpureloc : IsPurelyInseparable r.ResidueField r'.ResidueField := by
    rw [← RingHom.isPurelyInseparable_algebraMap_iff, residue_algebraMap_eq_map r r']
    exact RingHom.isPurelyInseparable_of_surjective _ hbij.2
  let _ : IsPurelyInseparable p₁.ResidueField r.ResidueField := hpure₂
  let _ : IsPurelyInseparable r.ResidueField r'.ResidueField := hpureloc
  exact IsPurelyInseparable.trans p₁.ResidueField r.ResidueField r'.ResidueField

/-- **Base change of the fibre data along an étale extension.** If the fibre of `A → B` over `p`
has bijective spectrum map and purely inseparable residue extensions, then so has the fibre of
`R₁ ⊗[R] A → R₁ ⊗[R] B` over any prime `p₁` of `R₁` lying over `p`. -/
private lemma fiber_baseChange_comap_bijective_and_isPurelyInseparable
    {R : Type u} {R₁ : Type u₁} {A : Type v} {B : Type w}
    [CommRing R] [CommRing R₁] [CommRing A] [CommRing B]
    [Algebra R R₁] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.IsIntegral R A] [Algebra.IsIntegral R B]
    (p : Ideal R) [p.IsPrime] (p₁ : Ideal R₁) [p₁.IsPrime] [p₁.LiesOver p]
    (hbij : Function.Bijective (PrimeSpectrum.comap
      (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom R A B) :
        p.Fiber A →ₐ[p.ResidueField] p.Fiber B).toRingHom))
    (hins : ∀ (P : Ideal (p.Fiber A)) [P.IsPrime] (Q : Ideal (p.Fiber B)) [Q.IsPrime]
      (h : P = Q.comap (Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
        (IsScalarTower.toAlgHom R A B) :
        p.Fiber A →ₐ[p.ResidueField] p.Fiber B).toRingHom),
      (Ideal.ResidueField.map P Q (Algebra.TensorProduct.map
        (AlgHom.id p.ResidueField p.ResidueField) (IsScalarTower.toAlgHom R A B) :
        p.Fiber A →ₐ[p.ResidueField] p.Fiber B).toRingHom h).IsPurelyInseparable) :
    let φ : (R₁ ⊗[R] A) →ₐ[R₁] (R₁ ⊗[R] B) :=
      Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (IsScalarTower.toAlgHom R A B)
    let f₁ : p₁.Fiber (R₁ ⊗[R] A) →ₐ[p₁.ResidueField] p₁.Fiber (R₁ ⊗[R] B) :=
      Algebra.TensorProduct.map (AlgHom.id p₁.ResidueField p₁.ResidueField) φ
    Function.Bijective (PrimeSpectrum.comap f₁.toRingHom) ∧
      ∀ (P : Ideal (p₁.Fiber (R₁ ⊗[R] A))) [P.IsPrime]
        (Q : Ideal (p₁.Fiber (R₁ ⊗[R] B))) [Q.IsPrime]
        (h : P = Q.comap f₁.toRingHom),
        (Ideal.ResidueField.map P Q f₁.toRingHom h).IsPurelyInseparable := by
  intro φ' f₁'
  let fb : p.Fiber A →ₐ[p.ResidueField] p.Fiber B :=
    Algebra.TensorProduct.map (AlgHom.id p.ResidueField p.ResidueField)
      (IsScalarTower.toAlgHom R A B)
  let _ : Algebra (p.Fiber A) (p.Fiber B) := fb.toAlgebra
  let _ : IsScalarTower p.ResidueField (p.Fiber A) (p.Fiber B) :=
    .of_algebraMap_eq fun a => (fb.commutes a).symm
  have _i1 : Algebra.IsIntegral p.ResidueField (p.Fiber B) :=
    Algebra.IsIntegral.tensorProduct R p.ResidueField B
  have _i2 : Algebra.IsIntegral (p.Fiber A) (p.Fiber B) :=
    Algebra.IsIntegral.tower_top p.ResidueField
  let φ : (R₁ ⊗[R] A) →ₐ[R₁] (R₁ ⊗[R] B) :=
    Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (IsScalarTower.toAlgHom R A B)
  let _ : Algebra (R₁ ⊗[R] A) (R₁ ⊗[R] B) := φ.toAlgebra
  let _ : IsScalarTower R₁ (R₁ ⊗[R] A) (R₁ ⊗[R] B) :=
    .of_algebraMap_eq fun a => (φ.commutes a).symm
  have _i3 : Algebra.IsIntegral R₁ (R₁ ⊗[R] B) :=
    Algebra.IsIntegral.tensorProduct R R₁ B
  have _i4 : Algebra.IsIntegral (R₁ ⊗[R] A) (R₁ ⊗[R] B) :=
    Algebra.IsIntegral.tower_top R₁
  let _ : Algebra p.ResidueField p₁.ResidueField :=
    (Ideal.ResidueField.map p p₁ (algebraMap R R₁) (p₁.over_def p)).toAlgebra
  let _ : IsScalarTower R p.ResidueField p₁.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      simp [RingHom.algebraMap_toAlgebra,
        IsScalarTower.algebraMap_apply R R₁ p₁.ResidueField]
  let _ : Semiring (p₁.Fiber (R₁ ⊗[R] A)) :=
    (inferInstance : CommSemiring (p₁.Fiber (R₁ ⊗[R] A))).toSemiring
  let _ : Semiring (p₁.Fiber (R₁ ⊗[R] B)) :=
    (inferInstance : CommSemiring (p₁.Fiber (R₁ ⊗[R] B))).toSemiring
  let f₁ : p₁.Fiber (R₁ ⊗[R] A) →ₐ[p₁.ResidueField]
      p₁.Fiber (R₁ ⊗[R] B) :=
    Algebra.TensorProduct.map (AlgHom.id p₁.ResidueField p₁.ResidueField) φ
  let _ : Algebra (p₁.Fiber (R₁ ⊗[R] A))
      (p₁.Fiber (R₁ ⊗[R] B)) := f₁.toRingHom.toAlgebra
  let _ : Algebra (p.Fiber A) (p₁.Fiber (R₁ ⊗[R] A)) :=
    (fiberBaseChangeHom A p p₁).toAlgebra
  let _ : Algebra (p.Fiber B) (p₁.Fiber (R₁ ⊗[R] B)) :=
    (fiberBaseChangeHom B p p₁).toAlgebra
  have hf₁_fD : f₁.toRingHom.comp (fiberBaseChangeHom A p p₁) =
      (fiberBaseChangeHom B p p₁).comp fb.toRingHom :=
    fiberBaseChangeHom_comm p p₁ (IsScalarTower.toAlgHom R A B)
  let _ : Algebra (p.Fiber A) (p₁.Fiber (R₁ ⊗[R] B)) :=
    ((fiberBaseChangeHom B p p₁).comp fb.toRingHom).toAlgebra
  have _i : IsScalarTower (p.Fiber A) (p.Fiber B)
      (p₁.Fiber (R₁ ⊗[R] B)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _i : IsScalarTower (p.Fiber A) (p₁.Fiber (R₁ ⊗[R] A))
      (p₁.Fiber (R₁ ⊗[R] B)) :=
    IsScalarTower.of_algebraMap_eq' hf₁_fD.symm
  let _ : Algebra p.ResidueField (p₁.Fiber (R₁ ⊗[R] A)) :=
    Algebra.compHom _ (algebraMap p.ResidueField p₁.ResidueField)
  let _ : Algebra p.ResidueField (p₁.Fiber (R₁ ⊗[R] B)) :=
    Algebra.compHom _ (algebraMap p.ResidueField p₁.ResidueField)
  let _ : SMul p.ResidueField (p.Fiber A) :=
    (inferInstance : Algebra p.ResidueField (p.Fiber A)).toSMul
  let _ : SMul p.ResidueField (p.Fiber B) :=
    (inferInstance : Algebra p.ResidueField (p.Fiber B)).toSMul
  let _ : SMul p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] A)) :=
    (inferInstance : Algebra p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] A))).toSMul
  let _ : SMul p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] B)) :=
    (inferInstance : Algebra p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] B))).toSMul
  let _ : SMul p.ResidueField (p₁.Fiber (R₁ ⊗[R] A)) :=
    (inferInstance : Algebra p.ResidueField (p₁.Fiber (R₁ ⊗[R] A))).toSMul
  let _ : SMul p.ResidueField (p₁.Fiber (R₁ ⊗[R] B)) :=
    (inferInstance : Algebra p.ResidueField (p₁.Fiber (R₁ ⊗[R] B))).toSMul
  have _i : IsScalarTower p.ResidueField p₁.ResidueField
      (p₁.Fiber (R₁ ⊗[R] A)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _i : IsScalarTower p.ResidueField p₁.ResidueField
      (p₁.Fiber (R₁ ⊗[R] B)) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _i : IsScalarTower p.ResidueField (p.Fiber A)
      (p₁.Fiber (R₁ ⊗[R] A)) :=
    IsScalarTower.of_algebraMap_eq' (fiberBaseChangeHom_comp_algebraMap A p p₁).symm
  have _i : IsScalarTower p.ResidueField (p.Fiber B)
      (p₁.Fiber (R₁ ⊗[R] B)) :=
    IsScalarTower.of_algebraMap_eq' (fiberBaseChangeHom_comp_algebraMap B p p₁).symm
  have hpushD : Algebra.IsPushout p.ResidueField p₁.ResidueField
      (p.Fiber A) (p₁.Fiber (R₁ ⊗[R] A)) := isPushout_fiberBaseChangeHom A p p₁
  have hpushS : Algebra.IsPushout p.ResidueField p₁.ResidueField
      (p.Fiber B) (p₁.Fiber (R₁ ⊗[R] B)) := isPushout_fiberBaseChangeHom B p p₁
  let _ : Algebra.IsPushout p.ResidueField (p.Fiber A) p₁.ResidueField
      (p₁.Fiber (R₁ ⊗[R] A)) := Algebra.IsPushout.symm hpushD
  have _i : IsScalarTower p.ResidueField (p₁.Fiber (R₁ ⊗[R] A))
      (p₁.Fiber (R₁ ⊗[R] B)) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (f₁.commutes (algebraMap p.ResidueField p₁.ResidueField x)).symm
  have _i : IsScalarTower p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] A))
      (p₁.Fiber (R₁ ⊗[R] B)) :=
    IsScalarTower.of_algebraMap_eq fun x => (f₁.commutes x).symm
  have _i : Algebra.IsPushout (p.Fiber A) (p.Fiber B)
      (p₁.Fiber (R₁ ⊗[R] A)) (p₁.Fiber (R₁ ⊗[R] B)) :=
    (Algebra.IsPushout.comp_iff p.ResidueField (p.Fiber A)
      p₁.ResidueField (p₁.Fiber (R₁ ⊗[R] A))).mp
        (Algebra.IsPushout.symm hpushS)
  have hd :=
    (PrimeSpectrum.isHomeomorph_comap_and_baseChange_of_bijective_comap_of_isPurelyInseparable
      hbij hins).2
      (p₁.Fiber (R₁ ⊗[R] A)) (p₁.Fiber (R₁ ⊗[R] B))
  exact ⟨hd.2.1, hd.2.2⟩

/-- **No prime over `p₁` forces the base change to vanish after a further localization.** If the
base change `R₁ ⊗[R] D` of a module-finite intermediate algebra has no prime over `p₁`, then
after inverting one element of `R₁ \ p₁` the base change of `S` is the zero ring. -/
private lemma exists_etale_completeOrthogonalIdempotents_of_no_prime
    {R : Type u} {S : Type v} {D : Type w} [CommRing R] [CommRing S] [CommRing D]
    [Algebra R S] [Algebra R D] [Algebra D S] [IsScalarTower R D S]
    [Algebra.IsIntegral R S] [Algebra.IsIntegral R D]
    (p : Ideal R) [p.IsPrime]
    (R₁ : Type u) [CommRing R₁] [Algebra R R₁] [Algebra.Etale R R₁]
    (p₁ : Ideal R₁) [hp₁ : p₁.IsPrime] [p₁.LiesOver p]
    (hno : ∀ (Q : Ideal (R₁ ⊗[R] D)), Q.IsPrime → Q.LiesOver p₁ →
      (1 : R₁ ⊗[R] D) ∈ Q) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p) (n : ℕ)
      (e : Fin n → R' ⊗[R] S) (_ : CompleteOrthogonalIdempotents e)
      (r : (i : Fin n) → Ideal (Localization.Away (e i)))
      (_ : ∀ i, (r i).IsPrime) (_ : ∀ i, (r i).LiesOver p'),
      (∀ i : Fin n, Algebra.IsIntegral R' (Localization.Away (e i))) ∧
      (∀ (i : Fin n) (q : Ideal (Localization.Away (e i))),
        q.IsPrime → q.LiesOver p' → q = r i) ∧
      ∀ i : Fin n,
        let _ := Localization.AtPrime.algebraOfLiesOver p' (r i)
        IsPurelyInseparable p'.ResidueField (r i).ResidueField := by
  classical
  let _ : Algebra.IsIntegral R₁ (R₁ ⊗[R] D) :=
    Algebra.IsIntegral.tensorProduct R R₁ D
  let φ : (R₁ ⊗[R] D) →ₐ[R₁] (R₁ ⊗[R] S) :=
    Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (IsScalarTower.toAlgHom R D S)
  have hker_not : ¬ RingHom.ker (algebraMap R₁ (R₁ ⊗[R] D)) ≤ p₁ := by
    intro hk
    obtain ⟨Q, _, hQ, hQo⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral p₁ (⊥ : Ideal (R₁ ⊗[R] D))
        (by simpa only [← RingHom.ker_eq_comap_bot] using hk)
    let _ : Q.IsPrime := hQ
    let _ : Q.LiesOver p₁ := ⟨hQo.symm⟩
    exact hQ.ne_top (Q.eq_top_iff_one.mpr (hno Q hQ inferInstance))
  obtain ⟨g, hgker, hgnot⟩ := IsConcreteLE.not_le_iff_exists.mp hker_not
  let R₂ := Localization.Away g
  let _ : Algebra R R₂ := Algebra.compHom _ (algebraMap R R₁)
  let _ : SMul R R₂ := (inferInstance : Algebra R R₂).toSMul
  let _ : SMul R₁ R₂ := (inferInstance : Algebra R₁ R₂).toSMul
  let _ : Module R R₂ := (inferInstance : Algebra R R₂).toModule
  have _i : IsScalarTower R R R₂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _i : IsScalarTower R R₁ R₂ := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  let _ : Algebra.Etale R R₂ := Algebra.Etale.comp R R₁ R₂
  let p₂ : Ideal R₂ := p₁.map (algebraMap R₁ R₂)
  have hdisj : Disjoint (Submonoid.powers g : Set R₁) (p₁ : Set R₁) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime g).2 hgnot
  let _ : p₂.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) R₂ p₁ hp₁ hdisj
  let _ : p₂.LiesOver p₁ :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (Submonoid.powers g) R₂ hdisj
  let _ : p₂.LiesOver p := Ideal.LiesOver.trans p₂ p₁ p
  have hgS : algebraMap R₁ (R₁ ⊗[R] S) g = 0 := by
    rw [← φ.commutes g, (RingHom.mem_ker).mp hgker, map_zero]
  let ψ : (R₁ ⊗[R] S) →ₐ[R] (R₂ ⊗[R] S) :=
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R R₁ R₂) (AlgHom.id R S)
  have hgzero :
      (Algebra.TensorProduct.includeLeft : R₂ →ₐ[R] R₂ ⊗[R] S)
        (algebraMap R₁ R₂ g) = 0 := by
    have h := congrArg ψ hgS
    simpa [ψ, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.map_tmul] using h
  have hunit : IsUnit
      ((Algebra.TensorProduct.includeLeft : R₂ →ₐ[R] R₂ ⊗[R] S)
        (algebraMap R₁ R₂ g)) :=
    (IsLocalization.Away.algebraMap_isUnit (S := R₂) g).map
      (Algebra.TensorProduct.includeLeft : R₂ →ₐ[R] R₂ ⊗[R] S).toRingHom
  have _s : Subsingleton (R₂ ⊗[R] S) :=
    (subsingleton_iff_zero_eq_one).1 ((isUnit_zero_iff).1 (hgzero ▸ hunit))
  let e₂ : Fin 0 → R₂ ⊗[R] S := Fin.elim0
  have he₂ : CompleteOrthogonalIdempotents e₂ := by
    rw [CompleteOrthogonalIdempotents.iff_ortho_complete]
    constructor
    · intro i
      exact Fin.elim0 i
    · exact Subsingleton.elim _ _
  let r₂ : (i : Fin 0) → Ideal (Localization.Away (e₂ i)) := fun i => Fin.elim0 i
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, p₂,
    inferInstance, inferInstance, 0, e₂, he₂, r₂, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

/-- **Splitting an integral algebra after an étale extension.**
If an integral `R`-algebra `S` has finitely many primes over `p`, and the maximal separable
subextension of every corresponding residue-field extension is finite, then after an étale base
change the algebra splits into integral factors having one prime over the chosen prime and purely
inseparable residue-field extensions. -/
@[stacks 0BSR]
public theorem exists_etale_completeOrthogonalIdempotents_integral_isPurelyInseparable
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (p : Ideal R) [p.IsPrime]
    (hfinite : Set.Finite {q : Ideal S | q.IsPrime ∧ q.LiesOver p})
    (hseparable : ∀ (q : Ideal S) (hq : q.IsPrime) (hqover : q.LiesOver p),
      letI := hq
      letI := hqover
      letI := Localization.AtPrime.algebraOfLiesOver p q
      Module.Finite p.ResidueField
        (separableClosure p.ResidueField q.ResidueField)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (p' : Ideal R') (_ : p'.IsPrime) (_ : p'.LiesOver p) (n : ℕ)
      (e : Fin n → R' ⊗[R] S) (_ : CompleteOrthogonalIdempotents e)
      (r : (i : Fin n) → Ideal (Localization.Away (e i)))
      (_ : ∀ i, (r i).IsPrime) (_ : ∀ i, (r i).LiesOver p'),
      (∀ i : Fin n, Algebra.IsIntegral R' (Localization.Away (e i))) ∧
      (∀ (i : Fin n) (q : Ideal (Localization.Away (e i))),
        q.IsPrime → q.LiesOver p' → q = r i) ∧
      ∀ i : Fin n,
        letI := Localization.AtPrime.algebraOfLiesOver p' (r i)
        IsPurelyInseparable p'.ResidueField (r i).ResidueField := by
  classical
  obtain ⟨D, _, _, _, _, hDfinite, hinjD, hcomapD, hpureD⟩ :=
    exists_moduleFinite_tower_residue_isPurelyInseparable p hfinite hseparable
  let : Module.Finite R D := hDfinite
  have : Algebra.IsIntegral R D := inferInstance
  have : Algebra.IsIntegral D S := Algebra.IsIntegral.tower_top R
  let : Algebra.FiniteType R D := Module.Finite.finiteType D
  have hring : ∀ (P : Ideal D) [P.IsPrime] [P.LiesOver p] (Q : Ideal S) [Q.IsPrime]
      [Q.LiesOver p] (hPQ : P = Q.comap (algebraMap D S)),
      (Ideal.ResidueField.map P Q (algebraMap D S) hPQ).IsPurelyInseparable := by
    intro P _ _ Q _ _ hPQ
    subst hPQ
    exact hpureD Q inferInstance inferInstance
  obtain ⟨R₁, hR₁, hA₁, hE₁, p₁, hp₁, hp₁p, n, d, hd, ρ, hρp, hρo,
      hfin, hρnot, hρuniq, hρpure, hlast⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_finite_isPurelyInseparable
      (S := D) p
  let : CommRing R₁ := hR₁
  let : Algebra R R₁ := hA₁
  let : Algebra.Etale R R₁ := hE₁
  let : p₁.IsPrime := hp₁
  let : p₁.LiesOver p := hp₁p
  have hnoLast (q : Ideal (R₁ ⊗[R] D)) [q.IsPrime] [q.LiesOver p₁] :
      d (Fin.last n) ∈ q := by
    by_contra hnot
    have hqf : Algebra.QuasiFiniteAt R₁ q := inferInstance
    exact hlast q inferInstance hnot hqf
  let φ : (R₁ ⊗[R] D) →ₐ[R₁] (R₁ ⊗[R] S) :=
    Algebra.TensorProduct.map (AlgHom.id R₁ R₁) (IsScalarTower.toAlgHom R D S)
  let : Algebra (R₁ ⊗[R] D) (R₁ ⊗[R] S) := φ.toAlgebra
  let : IsScalarTower R₁ (R₁ ⊗[R] D) (R₁ ⊗[R] S) :=
    .of_algebraMap_eq fun a => (φ.commutes a).symm
  have : Algebra.IsIntegral R₁ (R₁ ⊗[R] S) :=
    Algebra.IsIntegral.tensorProduct R R₁ S
  have : Algebra.IsIntegral (R₁ ⊗[R] D) (R₁ ⊗[R] S) :=
    Algebra.IsIntegral.tower_top R₁
  let f₁ : p₁.Fiber (R₁ ⊗[R] D) →ₐ[p₁.ResidueField]
      p₁.Fiber (R₁ ⊗[R] S) :=
    Algebra.TensorProduct.map (AlgHom.id p₁.ResidueField p₁.ResidueField) φ
  obtain ⟨hf₁bij, hf₁pure⟩ := fiber_baseChange_comap_bijective_and_isPurelyInseparable
    (A := D) (B := S) p p₁
    (fiber_comap_bijective_of_primesOver_comap_injective p hinjD hcomapD)
    (fiber_purelyInseparable_of_residue p hring)
  let FT := PrimeSpectrum.primesOverOrderIsoFiber R₁ (R₁ ⊗[R] D) p₁
  let FU := PrimeSpectrum.primesOverOrderIsoFiber R₁ (R₁ ⊗[R] S) p₁
  let : IsScalarTower R₁ (R₁ ⊗[R] D) (R₁ ⊗[R] S) :=
    IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have hf₁_pull (Q : PrimeSpectrum (p₁.Fiber (R₁ ⊗[R] S))) :
      (FT.symm (PrimeSpectrum.comap f₁.toRingHom Q) : Ideal (R₁ ⊗[R] D)) =
        (FU.symm Q : Ideal (R₁ ⊗[R] S)).comap φ.toRingHom :=
    fiber_prime_comap p₁ Q
  let lift (i : Fin n) : PrimeSpectrum (p₁.Fiber (R₁ ⊗[R] S)) :=
    Classical.choose (hf₁bij.2
      (FT ⟨ρ i, hρp i, hρo i⟩))
  let r (i : Fin n) : Ideal (R₁ ⊗[R] S) := (FU.symm (lift i) : Ideal (R₁ ⊗[R] S))
  have hrp (i : Fin n) : (r i).IsPrime := (FU.symm (lift i)).2.1
  have hro (i : Fin n) : (r i).LiesOver p₁ := (FU.symm (lift i)).2.2
  have hrcomap (i : Fin n) : (r i).comap φ.toRingHom = ρ i := by
    have h := hf₁_pull (lift i)
    have hch : PrimeSpectrum.comap f₁.toRingHom (lift i) =
        FT ⟨ρ i, hρp i, hρo i⟩ :=
      Classical.choose_spec (hf₁bij.2
        (FT ⟨ρ i, hρp i, hρo i⟩))
    rw [hch, FT.symm_apply_apply] at h
    exact h.symm
  have hlastT (Q : Ideal (R₁ ⊗[R] S)) [Q.IsPrime] [Q.LiesOver p₁] :
      φ (d (Fin.last n)) ∈ Q := by
    let : (Q.comap φ.toRingHom).LiesOver p₁ := liesOver_comap_algebraMap (D := R₁ ⊗[R] D) p₁ Q
    exact hnoLast (Q.comap φ.toRingHom)
  have hlastR (i : Fin n) : φ (d (Fin.last n)) ∈ r i := by
    let : (r i).IsPrime := hrp i
    let : (r i).LiesOver p₁ := hro i
    exact hlastT (r i)
  have hdmap : CompleteOrthogonalIdempotents (fun j => φ (d j)) := by
    change CompleteOrthogonalIdempotents (φ.toRingHom ∘ d)
    exact hd.map φ.toRingHom
  by_cases hn : 0 < n
  · let i₀ : Fin n := ⟨0, hn⟩
    let e : Fin n → R₁ ⊗[R] S := fun i =>
      if i = i₀ then φ (d i.castSucc) + φ (d (Fin.last n)) else φ (d i.castSucc)
    have he : CompleteOrthogonalIdempotents e :=
      completeOrthogonalIdempotents_merge_last (fun j => φ (d j)) hdmap hn
    have he_not (i : Fin n) : e i ∉ r i := by
      let : (r i).IsPrime := hrp i
      by_cases hi : i = i₀
      · have hnot := hρnot i
        rw [← hrcomap i] at hnot
        exact fun hmem => hnot (by simpa [e, hi] using (r i).sub_mem hmem (hlastR i))
      · simpa [e, hi, ← hrcomap i] using hρnot i
    have huniqT (i : Fin n) (Q : Ideal (R₁ ⊗[R] S))
        (hQ : Q.IsPrime) (hQo : Q.LiesOver p₁) (hQe : e i ∉ Q) : Q = r i := by
      let : Q.IsPrime := hQ
      let : Q.LiesOver p₁ := hQo
      have hcast : φ (d i.castSucc) ∉ Q := by
        by_cases hi : i = i₀
        · intro hmem
          apply hQe
          simpa [e, hi] using Q.add_mem hmem (hlastT Q)
        · simpa [e, hi] using hQe
      let : (Q.comap φ.toRingHom).LiesOver p₁ := liesOver_comap_algebraMap (D := R₁ ⊗[R] D) p₁ Q
      have hcomp : Q.comap φ.toRingHom = ρ i :=
        hρuniq i _ inferInstance inferInstance hcast
      have hQeq : (⟨Q, hQ, hQo⟩ : p₁.primesOver (R₁ ⊗[R] S)) =
          FU.symm (lift i) := by
        apply FU.injective
        apply (hf₁bij.1)
        apply FT.symm.injective
        apply Subtype.ext
        rw [FU.apply_symm_apply]
        change (FT.symm (PrimeSpectrum.comap f₁.toRingHom
          (FU ⟨Q, hQ, hQo⟩))).val =
          (FT.symm (PrimeSpectrum.comap f₁.toRingHom (lift i))).val
        calc
          _ = Q.comap φ.toRingHom := by
            simpa only [FU.symm_apply_apply] using
              hf₁_pull (FU ⟨Q, hQ, hQo⟩)
          _ = (r i).comap φ.toRingHom := hcomp.trans (hrcomap i).symm
          _ = _ := (hf₁_pull (lift i)).symm
      exact congrArg Subtype.val hQeq
    let r' (i : Fin n) : Ideal (Localization.Away (e i)) :=
      (r i).map (algebraMap (R₁ ⊗[R] S) (Localization.Away (e i)))
    have hfactor : ∀ i : Fin n,
        p₁.primesOver (Localization.Away (e i)) = {r' i} ∧
        ∀ (q : Ideal (Localization.Away (e i))) (hq : q.IsPrime) (hqo : q.LiesOver p₁),
          let _ := hq
          let _ := hqo
          let _ := Localization.AtPrime.algebraOfLiesOver p₁ q
          IsPurelyInseparable p₁.ResidueField q.ResidueField := by
      intro i
      let _ : (ρ i).IsPrime := hρp i
      let _ : (ρ i).LiesOver p₁ := hρo i
      let _ : (r i).IsPrime := hrp i
      let _ : (r i).LiesOver p₁ := hro i
      exact primesOver_away_eq_singleton_and_isPurelyInseparable p₁ (ρ i) (r i)
        (hrcomap i).symm (hρpure i).2 hf₁pure (e i) (he_not i) (huniqT i)
    have hr'mem (i : Fin n) : r' i ∈ p₁.primesOver (Localization.Away (e i)) := by
      rw [(hfactor i).1]
      exact Set.mem_singleton _
    have hr'prime (i : Fin n) : (r' i).IsPrime := (hr'mem i).1
    have hr'over (i : Fin n) : (r' i).LiesOver p₁ := (hr'mem i).2
    refine ⟨R₁, hR₁, hA₁, hE₁, p₁, hp₁, hp₁p, n, e, he, r',
      hr'prime, hr'over, ?_, ?_, ?_⟩
    · intro i
      exact integral_away_idempotent (e i) (he.idem i)
    · intro i q hq hqo
      have hmem : q ∈ p₁.primesOver (Localization.Away (e i)) := ⟨hq, hqo⟩
      rw [(hfactor i).1] at hmem
      exact hmem
    · intro i
      exact (hfactor i).2 (r' i) (hr'prime i) (hr'over i)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    exact exists_etale_completeOrthogonalIdempotents_of_no_prime p R₁ p₁ (fun Q hQ hQo => by
      let _ := hQ
      let _ := hQo
      have hdlast1 : d (Fin.last 0) = 1 := by
        simpa using hd.complete
      rw [← hdlast1]
      exact hnoLast Q)
end Algebra
