module

public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Bounding the dimension of the fibres of a ring map

For a fixed natural number `n`, the property that every fibre of a ring map has Krull dimension
at most `n` is local on the map.

## Main results

* `RingHom.fiberDimensionLE_propertyIsLocal` states the locality of the fibre-dimension bound.

## Implementation notes

The fibre over a prime `p` is `Ideal.Fiber p S`, namely `κ(p) ⊗[R] S`. Its dimension is
measured by `ringKrullDim`, so the zero ring (and hence an empty fibre) satisfies every
natural-number bound.

## References

* [Stacks Project, Tag 01SX](https://stacks.math.columbia.edu/tag/01SX)
-/

@[expose] public section

universe u

namespace RingHom

/-- A ring whose principal localizations along a spanning finite set all have Krull dimension
at most `n` has Krull dimension at most `n`. -/
private theorem ringKrullDim_le_of_localizations_of_span
    {B : Type u} [CommRing B] (n : WithBot ℕ∞) (s : Finset B)
    (hs : Ideal.span (s : Set B) = ⊤)
    (h : ∀ a ∈ s, ringKrullDim (Localization.Away a) ≤ n) :
    ringKrullDim B ≤ n := by
  rw [ringKrullDim_le_iff_height_le]
  intro p hp
  obtain ⟨a, has, hap⟩ : ∃ a ∈ s, a ∉ p := by
    by_contra! h'
    exact hp.ne_top (top_unique (hs ▸ Ideal.span_le.2 h'))
  have hd := (Ideal.disjoint_powers_iff_notMem_of_isPrime a).mpr hap
  let q : Ideal (Localization.Away a) := p.map (algebraMap B (Localization.Away a))
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ p hp hd
  have hunder : q.under B = p := by
    simpa [q] using IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers a) (Localization.Away a) hp hd
  rw [← hunder, IsLocalization.height_under (Submonoid.powers a) q]
  exact Ideal.height_le_ringKrullDim_of_isPrime.trans (h a has)

/-- The fibre of a simultaneous principal localization has the same dimension as the fibre of
the original map over the contracted prime. -/
private theorem ringKrullDim_fiber_away_eq
    {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (r : R) [Algebra R S] [Algebra R R'] [IsLocalization.Away r R']
    [Algebra S S'] [IsLocalization.Away (algebraMap R S r) S']
    [Algebra R' S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    (p' : Ideal R') [p'.IsPrime] :
    ringKrullDim (Ideal.Fiber p' S') =
      ringKrullDim (Ideal.Fiber (p'.under R) S) := by
  let p : Ideal R := p'.under R
  let eR := IsLocalization.orderIsoOfPrime (Submonoid.powers r) R'
  let eS := IsLocalization.orderIsoOfPrime (Submonoid.powers (algebraMap R S r)) S'
  have hrp : r ∉ p :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := p) r).mp (eR ⟨p', inferInstance⟩).2.2
  have hd (q : p.primesOver S) :
      Disjoint (Submonoid.powers (algebraMap R S r) : Set S) q.1 :=
    (Ideal.disjoint_powers_iff_notMem _ q.2.1.isRadical).mpr fun hq =>
      hrp ((Ideal.mem_of_liesOver q.1 p r).mpr (by simpa using hq))
  let eOver : p.primesOver S ≃o p'.primesOver S' := by
    refine
      { toFun := fun q => ?_
        invFun := fun q' => ?_
        left_inv := fun q => ?_
        right_inv := fun q' => ?_
        map_rel_iff' := ?_ }
    · let q' := eS.symm ⟨q.1, q.2.1, hd q⟩
      have : q'.1.IsPrime := q'.2
      have hqR : q'.1.under R = p := by
        rw [← Ideal.under_under (B := S), show q'.1.under S = q.1 from
          congrArg Subtype.val (eS.apply_symm_apply ⟨q.1, q.2.1, hd q⟩)]
        exact (Ideal.over_def q.1 p).symm
      have heq : eR ⟨q'.1.under R', inferInstance⟩ = eR ⟨p', inferInstance⟩ :=
        Subtype.ext ((Ideal.under_under (B := R') q'.1).trans hqR)
      exact ⟨q'.1, q'.2, ⟨(congrArg Subtype.val (eR.injective heq)).symm⟩⟩
    · let q := eS ⟨q'.1, q'.2.1⟩
      have : p'.LiesOver p := ⟨rfl⟩
      have : q'.1.LiesOver p := Ideal.LiesOver.trans q'.1 p' p
      have : q'.1.LiesOver q.1 := ⟨rfl⟩
      exact ⟨q.1, q.2.1, Ideal.LiesOver.tower_bot q'.1 q.1 p⟩
    · ext1
      dsimp
      exact congrArg Subtype.val (eS.apply_symm_apply ⟨q.1, q.2.1, hd q⟩)
    · ext1
      dsimp
      exact congrArg Subtype.val (eS.symm_apply_apply ⟨q'.1, q'.2.1⟩)
    · exact eS.symm.map_rel_iff
  simpa [ringKrullDim, p] using Order.krullDim_eq_of_orderIso
    ((PrimeSpectrum.primesOverOrderIsoFiber R' S' p').symm.trans
      (eOver.symm.trans (PrimeSpectrum.primesOverOrderIsoFiber R S p)))

/-- A localization has Krull dimension at most that of the ring it localizes. -/
private theorem ringKrullDim_localization_le
    {B T : Type u} [CommRing B] [CommRing T] (M : Submonoid B)
    [Algebra B T] [IsLocalization M T] :
    ringKrullDim T ≤ ringKrullDim B := by
  rw [ringKrullDim_le_iff_height_le]
  intro q hq
  rw [← IsLocalization.height_under M q]
  exact Ideal.height_le_ringKrullDim_of_isPrime

/-- Equal points of the prime spectrum have fibres of equal dimension. -/
private theorem ringKrullDim_fiber_eq_of_primeSpectrum_eq
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p q : PrimeSpectrum R) (h : p = q) :
    ringKrullDim (p.asIdeal.Fiber S) = ringKrullDim (q.asIdeal.Fiber S) :=
  h ▸ rfl

/-- A uniform bound on the Krull dimensions of the fibres is a local property of
commutative-ring homomorphisms. -/
@[stacks 01SX "fibre_dimension_bound_is_local"]
theorem fiberDimensionLE_propertyIsLocal (n : ℕ) :
    RingHom.StacksPropertyIsLocal
      (fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) =>
        letI : Algebra R S := f.toAlgebra
        ∀ (p : Ideal R) [p.IsPrime], ringKrullDim (p.Fiber S) ≤ (n : WithBot ℕ∞)) := by
  let P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop := fun {R S} _ _ f =>
    let : Algebra R S := f.toAlgebra
    ∀ (p : Ideal R) [p.IsPrime], ringKrullDim (p.Fiber S) ≤ (n : WithBot ℕ∞)
  change RingHom.StacksPropertyIsLocal P
  refine ⟨?_, ?_, ?_⟩
  · intro R S _ _ f r R' S' _ _ _ _ _ _ hf
    let : Algebra R S := f.toAlgebra
    intro p' _
    let f' : R' →+* S' := IsLocalization.Away.map R' S' f r
    let : Algebra R' S' := f'.toAlgebra
    let : Algebra R S' := (f'.comp (algebraMap R R')).toAlgebra
    have : IsScalarTower R R' S' := .of_algebraMap_eq' (by simp [RingHom.algebraMap_toAlgebra])
    have : IsScalarTower R S S' := .of_algebraMap_eq' (by
      change f'.comp (algebraMap R R') = (algebraMap S S').comp f
      ext x
      simp [f', IsLocalization.Away.map])
    change ringKrullDim (p'.Fiber S') ≤ (n : WithBot ℕ∞)
    rw [ringKrullDim_fiber_away_eq (S := S) (S' := S') r p']
    exact hf _
  · intro R A Rf Aa _ _ _ _ f a _ _ _ _ g hg
    let : Algebra Rf A := g.toAlgebra
    let g' : Rf →+* Aa := (algebraMap A Aa).comp g
    let : Algebra Rf Aa := g'.toAlgebra
    have : IsScalarTower Rf A Aa := .of_algebraMap_eq' rfl
    have htarget : P g' := by
      intro q _
      let e := IsLocalization.Away.tensorProductEquivTMulRight Rf q.ResidueField a Aa
      exact (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).trans_le
        ((ringKrullDim_localization_le
          (Submonoid.powers ((1 : q.ResidueField) ⊗ₜ[Rf] a))).trans (hg q))
    let F : R →+* Aa := g'.comp (algebraMap R Rf)
    let : Algebra R Aa := F.toAlgebra
    have hunitF : IsUnit (F f) := (IsLocalization.Away.algebraMap_isUnit f).map g'
    have : IsLocalization.Away (F f) Aa :=
      IsLocalization.away_of_isUnit_of_bijective (R := Aa) (S := Aa) hunitF Function.bijective_id
    have : IsScalarTower R Rf Aa := .of_algebraMap_eq' rfl
    have : IsScalarTower R Aa Aa := .of_algebraMap_eq' (by simp)
    intro p hp
    by_cases hfp : f ∈ p
    · have hz : (1 : p.ResidueField) ⊗ₜ[R] algebraMap R Aa f = 0 := by
        rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
        simp [Ideal.algebraMap_residueField_eq_zero.mpr hfp]
      obtain ⟨b, hb⟩ : ∃ b, algebraMap R Aa f * b = 1 := hunitF.exists_right_inv
      have : Subsingleton (p.Fiber Aa) := subsingleton_of_zero_eq_one <| by
        simpa [Algebra.TensorProduct.one_def, hb] using
          congrArg (· * (1 : p.ResidueField) ⊗ₜ[R] b) hz.symm
      rw [ringKrullDim_eq_bot_of_subsingleton]
      exact bot_le
    · let eR := IsLocalization.orderIsoOfPrime (Submonoid.powers f) Rf
      let q' := eR.symm ⟨p, hp, (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfp⟩
      have : q'.1.IsPrime := q'.2
      have hunder : q'.1.under R = p := congrArg Subtype.val (eR.apply_symm_apply _)
      exact (ringKrullDim_fiber_eq_of_primeSpectrum_eq ⟨p, hp⟩
        ⟨_, Ideal.IsPrime.comap (algebraMap R Rf)⟩
        (PrimeSpectrum.ext hunder.symm)).trans_le
        ((ringKrullDim_fiber_away_eq (S := Aa) (S' := Aa) f q'.1).symm.trans_le (htarget q'.1))
  · intro R S _ _ f s hs hloc
    classical
    let : Algebra R S := f.toAlgebra
    intro p _
    let t : Finset (p.Fiber S) := s.image (fun a => (1 : p.ResidueField) ⊗ₜ[R] (a : S))
    have ht : Ideal.span (t : Set (p.Fiber S)) = ⊤ := by
      have hmap := congrArg (Ideal.map (Algebra.TensorProduct.includeRight
        (R := R) (A := p.ResidueField) (B := S)).toRingHom) hs
      rw [Ideal.map_span, Ideal.map_top] at hmap
      change Ideal.span ((fun a : S => (1 : p.ResidueField) ⊗ₜ[R] a) '' (s : Set S)) = ⊤ at hmap
      simpa [t, Finset.coe_image] using hmap
    refine ringKrullDim_le_of_localizations_of_span _ t ht
      (Finset.forall_mem_image.2 fun a ha => ?_)
    let S' := Localization.Away a
    let f' : R →+* S' := (algebraMap S S').comp f
    let : Algebra R S' := f'.toAlgebra
    let : SMul R S' := f'.toAlgebra.toSMul
    let : Module R S' := f'.toAlgebra.toModule
    have : IsScalarTower R S S' := .of_algebraMap_eq' rfl
    let e := IsLocalization.Away.tensorProductEquivTMulRight R p.ResidueField a S'
    exact (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm.trans_le (hloc ⟨a, ha⟩ p)

end RingHom
