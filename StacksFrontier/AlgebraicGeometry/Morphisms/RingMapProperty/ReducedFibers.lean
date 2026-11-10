module

public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Ring maps with reduced fibres

A ring map has reduced fibres if its fibre ring at every prime of the source is reduced. This
property is local in the sense of the Stacks Project.

## Main definitions

* `RingHom.ReducedFibers` means that every prime fibre of a ring map is reduced.

## Main results

* `RingHom.reducedFibers_propertyIsLocal` states locality of reduced fibres.

## Implementation notes

The fibre at a prime is Mathlib's `Ideal.Fiber`, formed using the algebra structure induced by
the ring map. Locality uses all three conditions of `RingHom.StacksPropertyIsLocal`.

## References

* [Stacks Project, Tag 01SX](https://stacks.math.columbia.edu/tag/01SX)
-/

@[expose] public section

universe u

namespace RingHom

/-- Every fibre ring of a ring homomorphism over a prime of its source is reduced. -/
def ReducedFibers {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  let : Algebra R S := f.toAlgebra
  ∀ (p : Ideal R) [p.IsPrime], IsReduced (p.Fiber S)

/-- Base change of a principal localization of the source, as an algebra equivalence onto the
corresponding localization of the target. -/
private noncomputable def baseChangeAwayAlgEquiv
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] (r : R) [Algebra R R'] [IsLocalization.Away r R']
    [Algebra S S'] [IsLocalization.Away ((algebraMap R S) r) S']
    [Algebra R S'] [Algebra R' S'] [IsScalarTower R R' S'] [IsScalarTower R S S'] :
    TensorProduct R R' S ≃ₐ[R'] S' := by
  let : Algebra S (TensorProduct R R' S) := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization.Away ((algebraMap R S) r) (TensorProduct R R' S) := by
    infer_instance
  let eS : TensorProduct R R' S ≃ₐ[S] S' :=
    IsLocalization.algEquiv (Submonoid.powers ((algebraMap R S) r)) _ _
  let φ : TensorProduct R R' S →ₐ[R'] S' :=
    Algebra.TensorProduct.lift (Algebra.ofId R' S') (IsScalarTower.toAlgHom R S S')
      (fun _ _ => Commute.all _ _)
  have hφ (x : S) : φ (Algebra.TensorProduct.includeRight x) = algebraMap S S' x := by
    simp [φ]
  have hmaps : φ.toRingHom.comp (algebraMap S (TensorProduct R R' S)) =
      eS.toRingHom.comp (algebraMap S (TensorProduct R R' S)) := by
    ext x
    change φ (Algebra.TensorProduct.includeRight x) = eS (algebraMap S (TensorProduct R R' S) x)
    rw [hφ, eS.commutes]
  have heq : φ.toRingHom = eS.toRingHom :=
    IsLocalization.ringHom_ext (Submonoid.powers ((algebraMap R S) r)) hmaps
  have hbij : Function.Bijective φ := by
    change Function.Bijective φ.toRingHom
    rw [heq]
    exact eS.toRingEquiv.bijective
  exact AlgEquiv.ofBijective φ hbij

/-- The fibre of a simultaneous principal localization agrees with the fibre of the original
map over the contracted prime. -/
private noncomputable def fiberAwayEquiv
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] (r : R) [Algebra R R'] [IsLocalization.Away r R']
    [Algebra S S'] [IsLocalization.Away ((algebraMap R S) r) S']
    [Algebra R S'] [Algebra R' S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (q : Ideal R') [q.IsPrime] :
    let p := q.comap (algebraMap R R')
    q.Fiber S' ≃+* p.Fiber S := by
  let p := q.comap (algebraMap R R')
  have : p.IsPrime := Ideal.comap_isPrime (algebraMap R R') q
  let eRes : p.ResidueField ≃ₐ[R] q.ResidueField :=
    AlgEquiv.ofBijective (Ideal.ResidueField.mapₐ p q (Algebra.ofId R R') rfl)
      (RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        (RingHom.surjectiveOnStalks_of_isLocalization (Submonoid.powers r) R') p q rfl)
  let eTarget : TensorProduct R R' S ≃ₐ[R'] S' :=
    baseChangeAwayAlgEquiv (R := R) (S := S) (R' := R') (S' := S') r
  let eTensor : TensorProduct R' q.ResidueField S' ≃ₐ[q.ResidueField]
      TensorProduct R' q.ResidueField (TensorProduct R R' S) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl (R := q.ResidueField)) eTarget.symm
  let eCancel : TensorProduct R' q.ResidueField (TensorProduct R R' S) ≃ₐ[q.ResidueField]
      TensorProduct R q.ResidueField S :=
    Algebra.TensorProduct.cancelBaseChange R R' q.ResidueField q.ResidueField S
  let eField : TensorProduct R p.ResidueField S ≃ₐ[R]
      TensorProduct R q.ResidueField S :=
    Algebra.TensorProduct.congr eRes (AlgEquiv.refl (R := R) (A₁ := S))
  exact eTensor.toRingEquiv.trans <| eCancel.toRingEquiv.trans eField.toRingEquiv.symm

/-- The image of `f` in an algebra over the localization of `R` away from `f` is a unit. -/
private theorem isUnit_algebraMap_of_away {R A R' : Type u} [CommRing R] [CommRing A]
    [CommRing R'] (f : R) [Algebra R R'] [IsLocalization.Away f R'] [Algebra R A] [Algebra R' A]
    [IsScalarTower R R' A] : IsUnit (algebraMap R A f) := by
  rw [IsScalarTower.algebraMap_apply R R' A]
  exact (IsLocalization.Away.algebraMap_isUnit f).map _

/-- When the target is already a localization away from the image of `f`, the fibre over a prime
of a principal localization of the source agrees with the fibre over the contracted prime. -/
private noncomputable def fiberSourceAwayEquiv
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
    (f : R) [Algebra R R'] [IsLocalization.Away f R']
    [Algebra R A] [Algebra R' A] [IsScalarTower R R' A]
    (p : Ideal R) [p.IsPrime] (q : Ideal R') [q.IsPrime]
    (hq : p = q.comap (algebraMap R R')) :
    q.Fiber A ≃+* p.Fiber A := by
  let : IsLocalization.Away (algebraMap R A f) A :=
    IsLocalization.away_of_isUnit_of_bijective A (isUnit_algebraMap_of_away (R' := R') f)
      Function.bijective_id
  subst p
  exact fiberAwayEquiv (R := R) (S := A) (R' := R') (S' := A) f q

/-- A ring all of whose principal localizations along a spanning finite set are reduced is
itself reduced. -/
private theorem isReduced_of_away_cover {B : Type*} [CommRing B] (s : Finset B)
    (hs : Ideal.span (s : Set B) = ⊤)
    (hred : ∀ a ∈ s, IsReduced (Localization.Away a)) : IsReduced B := by
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro J hJ
  have hnot : ¬ ∀ a ∈ s, a ∈ J := fun hall ↦
    hJ.ne_top (top_le_iff.mp (hs.symm.trans_le (Ideal.span_le.mpr hall)))
  push Not at hnot
  obtain ⟨a, ha, haJ⟩ := hnot
  have hloc : algebraMap B (Localization.Away a) x = 0 :=
    (hred a ha).eq_zero _ (hx.map (algebraMap B (Localization.Away a)))
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers a)
    (Localization.Away a) x).mp hloc
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m : B) a).mp m.2
  have hm' : a ^ n * x = 0 := by rw [hn]; exact hm
  have hu : IsUnit (algebraMap B (Localization.AtPrime J) a) :=
    IsLocalization.map_units (Localization.AtPrime J) (⟨a, haJ⟩ : J.primeCompl)
  have hpow : (algebraMap B (Localization.AtPrime J) a)^n *
      algebraMap B (Localization.AtPrime J) x = 0 := by
    rw [← map_pow, ← map_mul, hm', map_zero]
  exact ((hu.pow n).mul_left_injective (by simpa [mul_comm] using hpow))

/-- Having reduced fibres is local for ring homomorphisms. -/
@[stacks 01SX "reduced_fibres_is_local"]
theorem reducedFibers_propertyIsLocal :
    RingHom.StacksPropertyIsLocal (fun f => RingHom.ReducedFibers f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro R S _ _ f r R' S' _ _ _ _ _ _ hred
    let : Algebra R S := f.toAlgebra
    change ∀ (p : Ideal R) [p.IsPrime], IsReduced (p.Fiber S) at hred
    let g : R' →+* S' := IsLocalization.Away.map R' S' f r
    let : Algebra R' S' := g.toAlgebra
    let : Algebra R S' := ((algebraMap S S').comp f).toAlgebra
    have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq' rfl
    have hmap : g.comp (algebraMap R R') = (algebraMap S S').comp f := by
      simp [g, IsLocalization.Away.map]
    have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq' hmap.symm
    change ∀ (q : Ideal R') [q.IsPrime], IsReduced (q.Fiber S')
    intro q _
    have he : q.Fiber S' ≃+* (q.comap (algebraMap R R')).Fiber S :=
      fiberAwayEquiv (R := R) (S := S) (R' := R') (S' := S') r q
    exact isReduced_of_injective he he.injective
  · intro R A Rf Aa _ _ _ _ f a _ _ _ _ g hg
    let : Algebra Rf A := g.toAlgebra
    change ∀ (q : Ideal Rf) [q.IsPrime], IsReduced (q.Fiber A) at hg
    let gR : R →+* A := g.comp (algebraMap R Rf)
    let : Algebra R A := gR.toAlgebra
    have : IsScalarTower R Rf A := IsScalarTower.of_algebraMap_eq' rfl
    let gAa : Rf →+* Aa := (algebraMap A Aa).comp g
    let h : R →+* Aa := gAa.comp (algebraMap R Rf)
    let : Algebra Rf Aa := gAa.toAlgebra
    let : Algebra R Aa := h.toAlgebra
    have : IsScalarTower R Rf Aa := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower Rf A Aa := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower R A Aa := IsScalarTower.of_algebraMap_eq' rfl
    change ∀ (p : Ideal R) [p.IsPrime], IsReduced (p.Fiber Aa)
    intro p hp
    let : Algebra Aa (p.Fiber Aa) := Algebra.TensorProduct.rightAlgebra
    have : IsScalarTower R Aa (p.Fiber Aa) := by
      apply IsScalarTower.of_algebraMap_eq'
      ext x
      change algebraMap R p.ResidueField x ⊗ₜ[R] (1 : Aa) =
        (1 : p.ResidueField) ⊗ₜ[R] algebraMap R Aa x
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    by_cases hf : f ∈ p
    · have hres : algebraMap R p.ResidueField f = 0 :=
        Ideal.algebraMap_residueField_eq_zero.mpr hf
      have hzero : algebraMap R (p.Fiber Aa) f = 0 := by
        rw [IsScalarTower.algebraMap_apply R p.ResidueField (p.Fiber Aa), hres, map_zero]
      have hunit : IsUnit (algebraMap R (p.Fiber Aa) f) := by
        simpa [IsScalarTower.algebraMap_apply R Aa (p.Fiber Aa)] using
          (isUnit_algebraMap_of_away (R' := Rf) f).map (algebraMap Aa (p.Fiber Aa))
      have : Subsingleton (p.Fiber Aa) :=
        subsingleton_of_zero_eq_one (by simpa [hzero] using hunit)
      infer_instance
    · let q : Ideal Rf := p.map (algebraMap R Rf)
      have hd : Disjoint (Submonoid.powers f : Set R) (p : Set R) :=
        (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
      have : q.IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) Rf p hp hd
      have hq : p = q.comap (algebraMap R Rf) := by
        simpa [q] using
          (IsLocalization.under_map_of_isPrime_disjoint
            (Submonoid.powers f) Rf hp hd).symm
      have hredP : IsReduced (p.Fiber A) := isReduced_of_injective _
        (fiberSourceAwayEquiv (R := R) (A := A) (R' := Rf) f p q hq).symm.injective
      have : IsReduced (Localization.Away ((1 : p.ResidueField) ⊗ₜ[R] a)) :=
        isReduced_localizationPreserves (Submonoid.powers ((1 : p.ResidueField) ⊗ₜ[R] a))
          (Localization.Away ((1 : p.ResidueField) ⊗ₜ[R] a)) hredP
      exact isReduced_of_injective _
        (IsLocalization.Away.tensorProductEquivTMulRight R p.ResidueField a Aa).injective
  · intro R S _ _ f s hs hsred
    dsimp [RingHom.ReducedFibers] at hsred ⊢
    algebraize [f]
    intro p hp
    classical
    let B := p.Fiber S
    let t : Finset B := s.image (fun a => (1 : p.ResidueField) ⊗ₜ[R] a)
    have ht : Ideal.span (t : Set B) = ⊤ := by
      rw [← Ideal.map_top (Algebra.TensorProduct.includeRight.toRingHom : S →+* B),
        ← hs, Ideal.map_span]
      congr 1
      ext x
      simp [t, Algebra.TensorProduct.includeRight_apply]
    apply isReduced_of_away_cover t ht
    intro b hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    let r : s := ⟨a, ha⟩
    let g : R →+* Localization.Away (r : S) :=
      (algebraMap S (Localization.Away (r : S))).comp f
    let algRS' : Algebra R (Localization.Away (r : S)) := g.toAlgebra
    let : Algebra R (Localization.Away (r : S)) := algRS'
    let : SMul R (Localization.Away (r : S)) := algRS'.toSMul
    let : Module R (Localization.Away (r : S)) := Algebra.toModule
    have : IsScalarTower R S (Localization.Away (r : S)) := IsScalarTower.of_algebraMap_eq' rfl
    let e := IsLocalization.Away.tensorProductEquivTMulRight R p.ResidueField (r : S)
      (Localization.Away (r : S))
    have : IsReduced (p.Fiber (Localization.Away (r : S))) := hsred r p
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end RingHom
