module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldSpecMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationFiniteFibres
public import StacksFrontier.RingTheory.Etale.IntegralSplitting
public import StacksFrontier.RingTheory.Etale.IntegralSplittingTensorField

/-!
# Splitting an integral morphism of affine schemes after an étale base change

Let `p : T ⟶ W` be an integral morphism of affine schemes which is surjectively dominated by a
compact scheme locally of finite type over `W`, and let `w ∈ W`.  This file proves the
geometric form of Stacks 0BSR used in the proof of Stacks 0E1D: after an étale base change
`τ : Spec R' ⟶ W` hitting `w` at `w₂`, the fibre product `P = T ×_W Spec R'` is the disjoint
union of finitely many open and closed pieces `E i`, each meeting the fibre over `w₂`, such that
over every field-valued point `ω : Spec Ω ⟶ Spec R'` at `w₂` each piece contributes at most one
point to `P ×_{Spec R'} Spec Ω`.

## Main results

* `AlgebraicGeometry.exists_etale_clopen_splitting_of_isIntegralHom`.

## Implementation notes

The ring of `W` is `R = Γ(W, ⊤)` and that of `T` is `A = Γ(T, ⊤)`; the morphism `p` is identified
with `Spec A ⟶ Spec R` through `Scheme.isoSpec`.  The fibre of `Spec A ⟶ Spec R` over `w` is
finite and its residue field extensions are finite, by the scheme-level core of Stacks 0E1C
(`AlgebraicGeometry.finite_preimage_singleton_of_surjective_of_locallyOfFiniteType`,
`AlgebraicGeometry.finite_residueFieldMap_of_surjective_of_locallyOfFiniteType`); these are the
hypotheses of Stacks 0BSR
(`Algebra.exists_etale_completeOrthogonalIdempotents_integral_isPurelyInseparable`), which gives
an étale `R → R'` and complete orthogonal idempotents `eᵢ` of `R' ⊗[R] A`.  Any fibre product
`P` is identified with `Spec (R' ⊗[R] A)`, and `E i` is the support of `eᵢ`, that is the range
of `Spec (R' ⊗[R] A)[1/eᵢ]`.  A point of `P ×_{Spec R'} Spec Ω` over `E i` comes from a point of
`Spec ((R' ⊗[R] A)[1/eᵢ] ⊗[R'] Ω)`, which has at most one point by
`Algebra.subsingleton_primeSpectrum_tensorProduct_field_of_isPurelyInseparable`.

## References

* [Stacks Project, Tag 0BSR](https://stacks.math.columbia.edu/tag/0BSR)
* [Stacks Project, Tag 0E1C](https://stacks.math.columbia.edu/tag/0E1C)
* [Stacks Project, Tag 0E1D](https://stacks.math.columbia.edu/tag/0E1D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

/-- The hypotheses of Stacks 0BSR, read off a morphism `Spec A ⟶ Spec R` with finite fibre
and finite residue field extensions over a prime `𝔭`. -/
theorem finite_primesOver_and_separableClosure_of_specMap {R A : CommRingCat.{u}}
    (φ : R ⟶ A) (𝔭 : PrimeSpectrum R)
    (hfin : ((Spec.map φ) ⁻¹' {𝔭}).Finite)
    (hres : ∀ q : Spec A, ((Spec.map φ).residueFieldMap q).hom.Finite) :
    letI := φ.hom.toAlgebra
    Set.Finite {q : Ideal A | q.IsPrime ∧ q.LiesOver 𝔭.asIdeal} ∧
      ∀ (q : Ideal A) (hq : q.IsPrime) (hqover : q.LiesOver 𝔭.asIdeal),
        letI := hq
        letI := hqover
        letI := Localization.AtPrime.algebraOfLiesOver 𝔭.asIdeal q
        Module.Finite 𝔭.asIdeal.ResidueField
          (separableClosure 𝔭.asIdeal.ResidueField q.ResidueField) := by
  let := φ.hom.toAlgebra
  refine ⟨?_, ?_⟩
  · refine (hfin.image fun x : Spec A => x.asIdeal).subset ?_
    rintro q ⟨hq, hqover⟩
    refine ⟨⟨q, hq⟩, ?_, rfl⟩
    change PrimeSpectrum.comap φ.hom ⟨q, hq⟩ = 𝔭
    exact PrimeSpectrum.ext hqover.over.symm
  · intro q hq hqover
    let := hq
    let := hqover
    let := Localization.AtPrime.algebraOfLiesOver 𝔭.asIdeal q
    obtain ⟨𝔭, h𝔭⟩ := 𝔭
    obtain rfl : 𝔭 = q.comap φ.hom := hqover.over
    have h := hres ⟨q, hq⟩
    rw [residueFieldMap_specMap] at h
    set M := Ideal.ResidueField.map (q.comap φ.hom) q φ.hom rfl
    set e₁ := Scheme.Spec.residueFieldIso R (PrimeSpectrum.comap φ.hom ⟨q, hq⟩)
    set e₂ := Scheme.Spec.residueFieldIso A ⟨q, hq⟩
    have hM : M = e₂.hom.hom.comp ((e₁.hom ≫ CommRingCat.ofHom M ≫ e₂.inv).hom.comp
        e₁.inv.hom) := by
      refine RingHom.ext fun x => ?_
      change M x = e₂.hom (e₂.inv (M (e₁.hom (e₁.inv x))))
      rw [Iso.inv_hom_id_apply]
      exact congrArg M (Iso.inv_hom_id_apply e₁ x).symm
    have hfinmap : M.Finite := by
      rw [hM]
      exact RingHom.Finite.comp (RingHom.Finite.of_surjective _
        e₂.commRingCatIsoToRingEquiv.surjective) (RingHom.Finite.comp h
          (RingHom.Finite.of_surjective _ e₁.commRingCatIsoToRingEquiv.symm.surjective))
    have : Module.Finite (q.comap φ.hom).ResidueField q.ResidueField :=
      RingHom.finite_algebraMap.mp hfinmap
    infer_instance

/-- Each prime of a commutative ring lies in the basic open of one of a complete family of
orthogonal idempotents. -/
private theorem _root_.PrimeSpectrum.exists_mem_basicOpen_of_completeOrthogonalIdempotents
    {B ι : Type*} [CommRing B] [Fintype ι] {e : ι → B} (he : CompleteOrthogonalIdempotents e)
    (x : PrimeSpectrum B) : ∃ i, x ∈ PrimeSpectrum.basicOpen (e i) := by
  by_contra! hx
  refine x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr ?_)
  rw [← he.complete]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_contra hne
  exact hx i ((PrimeSpectrum.mem_basicOpen _ _).mpr hne)

/-- The basic opens of two distinct orthogonal idempotents are disjoint. -/
private theorem _root_.PrimeSpectrum.disjoint_basicOpen_of_orthogonalIdempotents {B ι : Type*}
    [CommRing B] {e : ι → B} (he : OrthogonalIdempotents e) {i k : ι} (hik : i ≠ k) :
    Disjoint (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum B))
      (PrimeSpectrum.basicOpen (e k)) := by
  refine Set.disjoint_left.mpr fun x hxi hxk => ?_
  have hmem : x ∈ PrimeSpectrum.basicOpen (e i * e k) := by
    rw [PrimeSpectrum.basicOpen_mul]
    exact ⟨hxi, hxk⟩
  rw [he.ortho hik, PrimeSpectrum.basicOpen_zero] at hmem
  exact hmem

/-- The spectrum of a tensor product of algebras over `R` is the pullback of their spectra. -/
private theorem isPullback_specMap_tensorProduct (R S T : Type u) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : T →+* S ⊗[R] T)))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] T)))
      (Spec.map (CommRingCat.ofHom (algebraMap R T)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R S T)).flip

/-- Let `V` be the fibre product of `snd : P ⟶ Spec R'` with `Spec Ω ⟶ Spec R'`, and let
`j' : Spec C ⟶ P` lie over `Spec C ⟶ Spec R'`. If `C ⊗[R'] Ω` has at most one prime, then at
most one point of `V` lies over the range of `j'`. -/
private theorem eq_of_isPullback_of_subsingleton_primeSpectrum_tensorProduct {R' C Ω : Type u}
    [CommRing R'] [CommRing C] [Field Ω] [Algebra R' C] [Algebra R' Ω]
    [Subsingleton (PrimeSpectrum (C ⊗[R'] Ω))] {P V : Scheme.{u}} (snd : P ⟶ Spec (.of R'))
    (j' : Spec (.of C) ⟶ P) (hj' : j' ≫ snd = Spec.map (CommRingCat.ofHom (algebraMap R' C)))
    (a : V ⟶ P) (b : V ⟶ Spec (.of Ω))
    (hV : IsPullback a b snd (Spec.map (CommRingCat.ofHom (algebraMap R' Ω))))
    {v v' : V} (hv : a v ∈ Set.range j') (hv' : a v' ∈ Set.range j') : v = v' := by
  have hs := isPullback_specMap_tensorProduct R' C Ω
  rw [← hj'] at hs
  obtain ⟨c, hc⟩ := hv
  obtain ⟨c', hc'⟩ := hv'
  obtain ⟨d, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (hs.of_right' hV.flip) v c hc.symm
  obtain ⟨d', rfl, -⟩ := Scheme.exists_preimage_of_isPullback (hs.of_right' hV.flip) v' c' hc'.symm
  rw [Subsingleton.elim (α := PrimeSpectrum (C ⊗[R'] Ω)) d d']

/-- A field-valued point `ω` of `Spec R` whose image is the prime `p` corresponds to a ring map
`R → Ω` with kernel `p`. -/
private theorem ker_specPreimage_eq_of_forall_apply_eq {R Ω : Type u} [CommRing R] [Field Ω]
    {p : Ideal R} [p.IsPrime] (ω : Spec (.of Ω) ⟶ Spec (.of R))
    (hω : ∀ z, ω z = ⟨p, inferInstance⟩) : RingHom.ker (Spec.preimage ω).hom = p := by
  have h := congrArg PrimeSpectrum.asIdeal (hω ⟨⊥, Ideal.isPrime_bot⟩)
  rw [← Spec.map_preimage ω] at h
  change Ideal.comap (Spec.preimage ω).hom ⊥ = p at h
  rwa [← RingHom.ker_eq_comap_bot] at h

/-- **Étale-local splitting of an integral morphism of affine schemes** (Stacks 0BSR, in the form
used for Stacks 0E1D).  Let `p : T ⟶ W` be an integral morphism of affine schemes, surjectively
dominated by `g : U ⟶ T` with `U` compact and `g ≫ p` locally of finite type, and let `w ∈ W`.
There is an étale `τ : Spec R' ⟶ W` hitting `w` at `w₂` and a number `m` such that every fibre
product `P = T ×_W Spec R'` is covered by `m` pairwise disjoint open and closed sets `E i`, each
meeting the fibre over `w₂`, such that over any field-valued point `ω` of `Spec R'` at `w₂` each
`E i` has at most one point above it in `P ×_{Spec R'} Spec Ω`. -/
theorem exists_etale_clopen_splitting_of_isIntegralHom {U T W : Scheme.{u}} (g : U ⟶ T)
    (p : T ⟶ W) [IsAffine T] [IsAffine W] [IsIntegralHom p] [CompactSpace U]
    [LocallyOfFiniteType (g ≫ p)] (hg : Function.Surjective g) (w : W) :
    ∃ (R' : CommRingCat.{u}) (τ : Spec R' ⟶ W), Etale τ ∧ ∃ w₂ : Spec R', τ w₂ = w ∧
      ∃ m : ℕ, ∀ {P : Scheme.{u}} (fst : P ⟶ T) (snd : P ⟶ Spec R'), IsPullback fst snd p τ →
        ∃ E : Fin m → Set P, (∀ i, IsClopen (E i)) ∧
          (Pairwise fun i j => Disjoint (E i) (E j)) ∧ (∀ x, ∃ i, x ∈ E i) ∧
          (∀ i, ∃ x ∈ E i, snd x = w₂) ∧
          ∀ (Ω : Type u) [Field Ω] (ω : Spec (.of Ω) ⟶ Spec R'), (∀ z, ω z = w₂) →
            ∀ {V : Scheme.{u}} (a : V ⟶ P) (b : V ⟶ Spec (.of Ω)), IsPullback a b snd ω →
              ∀ (i : Fin m) (v v' : V), a v ∈ E i → a v' ∈ E i → v = v' := by
  classical
  -- the rings of `W` and `T`
  set R : CommRingCat.{u} := Γ(W, ⊤)
  set A : CommRingCat.{u} := Γ(T, ⊤)
  set φ : R ⟶ A := p.appTop
  let : Algebra R A := φ.hom.toAlgebra
  have hsq : T.isoSpec.hom ≫ Spec.map φ = p ≫ W.isoSpec.hom := Scheme.isoSpec_hom_naturality p
  have : IsIntegralHom (Spec.map φ) := by
    rw [show Spec.map φ = T.isoSpec.inv ≫ p ≫ W.isoSpec.hom by rw [← hsq, Iso.inv_hom_id_assoc]]
    infer_instance
  have hφint : φ.hom.IsIntegral := IsIntegralHom.SpecMap_iff.mp this
  have : Algebra.IsIntegral R A := ⟨fun x => hφint x⟩
  -- the scheme-level core of 0E1C for `Spec A ⟶ Spec R`
  set g' : U ⟶ Spec A := g ≫ T.isoSpec.hom
  have : LocallyOfFiniteType (g' ≫ Spec.map φ) := by
    rw [show g' ≫ Spec.map φ = (g ≫ p) ≫ W.isoSpec.hom by simp only [g', Category.assoc, hsq]]
    infer_instance
  have hg' : Function.Surjective g' := T.isoSpec.hom.homeomorph.surjective.comp hg
  set 𝔭 : PrimeSpectrum R := W.isoSpec.hom w
  obtain ⟨hfinite, hseparable⟩ := finite_primesOver_and_separableClosure_of_specMap φ 𝔭
    (finite_preimage_singleton_of_surjective_of_locallyOfFiniteType g' (Spec.map φ) hg' 𝔭)
    (finite_residueFieldMap_of_surjective_of_locallyOfFiniteType g' (Spec.map φ) hg')
  -- Stacks 0BSR
  obtain ⟨R', _, _, _, p', _, _, m, e, he, r, _, _, hrint, hruniq, hrpi⟩ :=
    Algebra.exists_etale_completeOrthogonalIdempotents_integral_isPurelyInseparable
      (R := R) (S := A) 𝔭.asIdeal hfinite hseparable
  -- the étale neighbourhood
  let ρ : R ⟶ CommRingCat.of R' := CommRingCat.ofHom (algebraMap R R')
  have hρ : Etale (Spec.map ρ) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr inferInstance)
  let w₂ : Spec (CommRingCat.of R') := ⟨p', inferInstance⟩
  have hρw₂ : Spec.map ρ w₂ = 𝔭 := PrimeSpectrum.ext (Ideal.over_def p' 𝔭.asIdeal).symm
  refine ⟨CommRingCat.of R', Spec.map ρ ≫ W.isoSpec.inv, inferInstance, w₂, ?_, m, ?_⟩
  · rw [Scheme.Hom.comp_apply, hρw₂, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  intro P fst snd hP
  -- `P` is `Spec (R' ⊗[R] A)`
  let B := R' ⊗[R] A
  have hcan := isPullback_specMap_tensorProduct R R' A
  have hP' : IsPullback (fst ≫ T.isoSpec.hom) snd (Spec.map φ) (Spec.map ρ) :=
    hP.of_iso (Iso.refl _) T.isoSpec (Iso.refl _) W.isoSpec (by simp) (by simp) hsq.symm
      (by simp)
  let ε : P ≅ Spec (CommRingCat.of B) := hP'.isoIsPullback _ _ hcan
  have hεsnd : ε.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : R' →+* B)) = snd :=
    IsPullback.isoIsPullback_hom_snd _ _ hP' hcan
  have hεinv : ε.inv ≫ snd = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : R' →+* B)) := by
    rw [← hεsnd, Iso.inv_hom_id_assoc]
  -- the pieces
  let C : Fin m → Type u := fun i => Localization.Away (e i)
  let j : ∀ i, Spec (CommRingCat.of (C i)) ⟶ Spec (CommRingCat.of B) := fun i =>
    Spec.map (CommRingCat.ofHom (algebraMap B (C i)))
  have hrange : ∀ i, Set.range (j i) = (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum B)) :=
    fun i => PrimeSpectrum.localization_away_comap_range (C i) (e i)
  have hj : ∀ i, j i ≫ ε.inv ≫ snd = Spec.map (CommRingCat.ofHom (algebraMap R' (C i))) := by
    intro i
    simp only [hεinv, j, ← Spec.map_comp]
    congr 1
  refine ⟨fun i => ε.hom ⁻¹' (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum B)),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => (PrimeSpectrum.isClopen_iff.mpr ⟨e i, he.idem i, rfl⟩).preimage ε.hom.continuous
  · exact fun i k hik => (PrimeSpectrum.disjoint_basicOpen_of_orthogonalIdempotents
      he.toOrthogonalIdempotents hik).preimage _
  · exact fun x => PrimeSpectrum.exists_mem_basicOpen_of_completeOrthogonalIdempotents he (ε.hom x)
  · intro i
    refine ⟨ε.inv (j i ⟨r i, inferInstance⟩), ?_, ?_⟩
    · change ε.hom (ε.inv _) ∈ (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum B))
      rw [← Scheme.Hom.comp_apply, ε.inv_hom_id, ← hrange]
      exact ⟨_, rfl⟩
    · change (j i ≫ ε.inv ≫ snd) ⟨r i, inferInstance⟩ = w₂
      rw [hj]
      exact PrimeSpectrum.ext (Ideal.over_def (r i) p').symm
  · intro Ω _ ω hω V a b hV i v v' hv hv'
    let : Algebra R' Ω := (Spec.preimage ω).hom.toAlgebra
    have := Algebra.subsingleton_primeSpectrum_tensorProduct_field_of_isPurelyInseparable p'
      (ker_specPreimage_eq_of_forall_apply_eq ω hω) (r i) (hruniq i) (hrpi i)
    have hmem : ∀ x : V, a x ∈ ε.hom ⁻¹' (PrimeSpectrum.basicOpen (e i) : Set (PrimeSpectrum B)) →
        a x ∈ Set.range (j i ≫ ε.inv) := by
      intro x hx
      obtain ⟨c, hc⟩ : ε.hom (a x) ∈ Set.range (j i) := by
        rw [hrange]
        exact hx
      refine ⟨c, ?_⟩
      rw [Scheme.Hom.comp_apply, hc, ← Scheme.Hom.comp_apply, ε.hom_inv_id]
      rfl
    rw [← Spec.map_preimage ω] at hV
    exact eq_of_isPullback_of_subsingleton_primeSpectrum_tensorProduct snd (j i ≫ ε.inv)
      ((Category.assoc _ _ _).trans (hj i)) a b hV (hmem v hv) (hmem v' hv')

end AlgebraicGeometry
