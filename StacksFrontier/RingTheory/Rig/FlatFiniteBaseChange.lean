module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Restricted.FiniteTypeBaseChange
public import StacksFrontier.RingTheory.Rig.ClosedPoint.CompletedTensorProductFlat
public import StacksFrontier.RingTheory.Rig.ClosedPoint.RestrictedPowerSeriesFlat
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Finite
public import StacksFrontier.Topology.Algebra.AdicTopology.EquivTransport

/-!
# Flatness of a tensor-product base change away from the closed locus

Let `A → B` and `A → C` be maps of adic topological rings and let `I` be an ideal of definition
of `A`.  If `B[1/a]` is flat over `A` for every topologically nilpotent `a : A` — the flatness
clause of naive rig-flatness — then `B ⊗[A] C` is flat over `C` after localizing at any prime
which avoids `I · (B ⊗[A] C)`.

The point is the usual base change for flatness (Tag 00HI).  A prime avoiding
`I · (B ⊗[A] C)` avoids the image of some `a ∈ I`; that `a` is topologically nilpotent, so
`B[1/a]` is flat over `A`, hence `C ⊗[A] B[1/a]` is flat over `C`; and that ring is the
localization of `B ⊗[A] C` away from the image of `a`, of which the localization at the prime
is a further localization.

## Main results

* `Rig.flat_localizationAway_tensorProduct_of_flat`: `(B ⊗[A] C)[1/a]` is flat over `C` when
  `B[1/a]` is flat over `A`.
* `Rig.flat_atPrime_tensorProduct_of_flat`: `(B ⊗[A] C)` is flat over `C` after localizing at
  any prime avoiding the extension of an ideal of definition whose topologically nilpotent
  elements are all flattening.

## Implementation notes

The identification of `(B ⊗[A] C)[1/a]` with `C ⊗[A] B[1/a]` is assembled from Mathlib's
`IsLocalization.Away.tensorProductEquivTMulRight`, which localizes the *right* factor, and the
flip `Algebra.TensorProduct.comm`; the flip is needed because the completed tensor product of
this development is written with the base-changed factor on the right, so `C` acts through
`Algebra.TensorProduct.rightAlgebra`.

## References

* [Stacks Project, Tag 0GGR](https://stacks.math.columbia.edu/tag/0GGR)
* [Stacks Project, Tag 00HI](https://stacks.math.columbia.edu/tag/00HI)
-/

@[expose] public section

namespace Rig

open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]

/-- **Base change for flatness after inverting an element of the base.**  If `B[1/a]` is flat
over `A` then `(B ⊗[A] C)[1/a]` is flat over `C`: the latter is `C ⊗[A] B[1/a]`, a base change
of a flat module. -/
public theorem flat_localizationAway_tensorProduct_of_flat (a : A)
    (hflat : Module.Flat A (Localization.Away (algebraMap A B a))) :
    Module.Flat C (Localization.Away (algebraMap A (B ⊗[A] C) a)) := by
  have h1 : Module.Flat C (C ⊗[A] Localization.Away (algebraMap A B a)) :=
    Module.Flat.baseChange A C (Localization.Away (algebraMap A B a))
  have he : (1 : C) ⊗ₜ[A] (algebraMap A B a) = algebraMap A (C ⊗[A] B) a := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (R := A) (A := B),
      Algebra.algebraMap_eq_smul_one (R := A) (A := C), TensorProduct.smul_tmul]
  have h2 : Module.Flat C (Localization.Away ((1 : C) ⊗ₜ[A] (algebraMap A B a))) :=
    Module.Flat.of_linearEquiv (IsLocalization.Away.tensorProductEquivTMulRight A C
      (algebraMap A B a) (Localization.Away (algebraMap A B a))).symm.toLinearEquiv
  rw [he] at h2
  have hmon : (Submonoid.powers (algebraMap A (B ⊗[A] C) a)).map
      (Algebra.TensorProduct.comm A B C).toRingEquiv.toMonoidHom =
      Submonoid.powers (algebraMap A (C ⊗[A] B) a) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers ((Algebra.TensorProduct.comm A B C).commutes a)
  exact Module.Flat.of_linearEquiv (AlgEquiv.ofRingEquiv
      (f := IsLocalization.ringEquivOfRingEquiv (Localization.Away (algebraMap A (B ⊗[A] C) a))
        (Localization.Away (algebraMap A (C ⊗[A] B) a))
        (Algebra.TensorProduct.comm A B C).toRingEquiv hmon) fun c => by
    rw [IsScalarTower.algebraMap_apply C (B ⊗[A] C)
        (Localization.Away (algebraMap A (B ⊗[A] C) a)),
      IsLocalization.ringEquivOfRingEquiv_eq hmon,
      IsScalarTower.algebraMap_apply C (C ⊗[A] B)
        (Localization.Away (algebraMap A (C ⊗[A] B) a))]
    rfl).toLinearEquiv

variable [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]

omit [IsTopologicalRing A] [IsLinearTopology A A] in
/-- **A tensor-product base change is flat over the second factor away from the closed
locus.**  If `B[1/a]` is flat over `A` for every topologically nilpotent `a : A`, then
`(B ⊗[A] C)_q` is flat over `C` at every prime `q` which does not contain the extension of an
ideal of definition `I` of `A`. -/
public theorem flat_atPrime_tensorProduct_of_flat (I : Ideal A)
    (hIdef : TopologicalRing.IsIdealOfDefinition I)
    (hflat : ∀ a : A, IsTopologicallyNilpotent a →
      Module.Flat A (Localization.Away (algebraMap A B a)))
    (q : Ideal (B ⊗[A] C)) [q.IsPrime]
    (hq : ¬ I.map (algebraMap A (B ⊗[A] C)) ≤ q) :
    _root_.RingHom.Flat
      ((algebraMap (B ⊗[A] C) (Localization.AtPrime q)).comp
        (algebraMap C (B ⊗[A] C))) := by
  -- an element of `I` whose image avoids `q`
  obtain ⟨a, ha, haq⟩ : ∃ a ∈ I, algebraMap A (B ⊗[A] C) a ∉ q := by
    by_contra hcon
    exact hq (Ideal.map_le_iff_le_comap.mpr fun a ha => by
      simpa using not_not.mp fun h => hcon ⟨a, ha, h⟩)
  have hnil : IsTopologicallyNilpotent a :=
    isTopologicallyNilpotent_of_mem_isIdealOfDefinition hIdef ha
  -- `(B ⊗[A] C)[1/a]` is flat over `C`
  have haway : _root_.RingHom.Flat
      ((algebraMap (B ⊗[A] C) (Localization.Away (algebraMap A (B ⊗[A] C) a))).comp
        (algebraMap C (B ⊗[A] C))) := by
    have h := flat_localizationAway_tensorProduct_of_flat (B := B) (C := C) a (hflat a hnil)
    rw [show (algebraMap (B ⊗[A] C) (Localization.Away (algebraMap A (B ⊗[A] C) a))).comp
          (algebraMap C (B ⊗[A] C)) =
        algebraMap C (Localization.Away (algebraMap A (B ⊗[A] C) a)) from
      (IsScalarTower.algebraMap_eq C (B ⊗[A] C)
        (Localization.Away (algebraMap A (B ⊗[A] C) a))).symm]
    exact _root_.RingHom.flat_algebraMap_iff.mpr h
  exact flat_atPrime_of_flat_away (algebraMap C (B ⊗[A] C))
    (algebraMap A (B ⊗[A] C) a) q haq haway

/-! ### Naive rig-flatness of the completed tensor product of a finite algebra -/

/-- Flatness at a prime travels along an isomorphism of the ring being localized, in the form
where the lower prime is named. -/
private theorem flat_atPrime_of_ringEquiv_of_eq {R R' S : Type u} [CommRing R] [CommRing R']
    [CommRing S] (e : R ≃+* R') (ι : S →+* R) (p : Ideal R) [p.IsPrime] (q : Ideal R')
    [q.IsPrime] (hpq : p = q.comap (e : R →+* R'))
    (h : _root_.RingHom.Flat
      ((algebraMap R' (Localization.AtPrime q)).comp ((e : R →+* R').comp ι))) :
    _root_.RingHom.Flat ((algebraMap R (Localization.AtPrime p)).comp ι) := by
  subst hpq
  exact flat_atPrime_comap_of_ringEquiv e ι q h

variable [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B] [IsNoetherianRing B]
  [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C] [IsNoetherianRing C]

/-- **Paragraph 2 of the proof of Tag 0GGR.**  If `C` is finite as an `A`-module then
`C → B ⊗̂[A] C` is naively rig-flat, given the flatness clause of naive rig-flatness for
`A → B`.

Adicness and topological finite type of the base-changed arrow are
`TopologicalRing.isAdic_and_isTopologicallyOfFiniteType_completedTensorProduct_baseChange`.  For
the flatness clause, `B ⊗̂[A] C` is `B ⊗[A] C` because `C` is finite
(`TopologicalRing.bijective_coe_completedTensorProduct_of_finite`), so the base change for
flatness of `Rig.flat_atPrime_tensorProduct_of_flat` applies there and transports across the
isomorphism; condition (3) of `Rig.naivelyRigFlat_tfae` then upgrades to condition (1). -/
public theorem isNaivelyRigFlat_completedTensorProduct_of_finite
    (I : Ideal A) (hIdef : TopologicalRing.IsIdealOfDefinition I)
    (hJ : _root_.IsAdic (I.map (algebraMap A B)))
    (hK : _root_.IsAdic (I.map (algebraMap A C)))
    [IsAdicComplete (I.map (algebraMap A B)) B] [Module.Finite A C]
    (hBw : TopologicalRing.IsWeaklyAdmissible B) (hCw : TopologicalRing.IsWeaklyAdmissible C)
    (hAB : Continuous (algebraMap A B)) (hAC : Continuous (algebraMap A C))
    (hABadic : _root_.RingHom.IsAdic (algebraMap A B))
    (hABft : TopologicalRing.IsTopologicallyOfFiniteType (algebraMap A B))
    (hflat : ∀ a : A, IsTopologicallyNilpotent a →
      Module.Flat A (Localization.Away (algebraMap A B a))) :
    RingHom.IsNaivelyRigFlat
      (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))) := by
  classical
  let : TopologicalSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductTopology (R := A) (M := B) (N := C)
  let : UniformSpace (B ⊗[A] C) :=
    TopologicalRing.tensorProductUniformSpace (R := A) (M := B) (N := C)
  have : IsUniformAddGroup (B ⊗[A] C) :=
    TopologicalRing.tensorProduct_isUniformAddGroup (R := A) (M := B) (N := C)
  obtain ⟨hcs, ht2⟩ :=
    TopologicalRing.completeSpace_and_t2Space_tensorProduct_of_finite I hJ hK
  let : CompleteSpace (B ⊗[A] C) := hcs
  let : T2Space (B ⊗[A] C) := ht2
  have hbij := TopologicalRing.bijective_coe_completedTensorProduct_of_finite I hJ hK
  obtain ⟨hDadic, hDft⟩ :=
    TopologicalRing.isAdic_and_isTopologicallyOfFiniteType_completedTensorProduct_baseChange
      hBw hCw ⟨I.map (algebraMap A C), Ideal.fg_of_isNoetherianRing _, hK⟩ hAB hAC
      ⟨hABadic, hABft⟩
  refine ⟨hDadic, hDft, ?_⟩
  -- the canonical map is an isomorphism of topological rings
  let e : (B ⊗[A] C) ≃+* TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C) :=
    RingEquiv.ofBijective UniformSpace.Completion.coeRingHom hbij
  have hcont : Continuous (e : (B ⊗[A] C) →
      TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)) :=
    UniformSpace.Completion.continuous_coe _
  have hcont' : Continuous (e.symm :
      TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C) → B ⊗[A] C) :=
    (TopologicalRing.homeomorphCompletion (α := B ⊗[A] C)).symm.continuous
  -- the extension of `I` is an ideal of definition of the completed tensor product
  have hLD : _root_.IsAdic (I.map (algebraMap A
      (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)))) := by
    have h := TopologicalRing.isAdic_map_of_ringEquiv e hcont hcont'
      (TopologicalRing.isAdic_tensorProduct_map_algebraMap I hJ hK)
    rwa [Ideal.map_map] at h
  have : Module.Finite B (B ⊗[A] C) := Module.Finite.base_change A B C
  have : IsNoetherianRing (B ⊗[A] C) := IsNoetherianRing.of_finite B (B ⊗[A] C)
  have : IsNoetherianRing
      (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)) :=
    isNoetherianRing_of_ringEquiv _ e
  have hDw := TopologicalRing.completedTensorProduct_isWeaklyAdmissible
    (B := A) (A := B) (C := C) hBw.1 hCw.1
  have hcrit := naivelyRigFlat_tfae
    (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C)))
    TopologicalRing.continuous_algebraMap_completedTensorProduct_right hCw hDw
    ⟨I.map (algebraMap A C), hK, Ideal.fg_of_isNoetherianRing _⟩
    ⟨I.map (algebraMap A _), hLD, Ideal.fg_of_isNoetherianRing _⟩ hDadic
  refine (hcrit.out 3 1).mp ?_
  intro p hp hJavoid
  let : p.IsPrime := hp
  obtain ⟨J, hJdef, hJp⟩ := hJavoid
  -- the extension of `I` avoids `p`
  have hJadic : _root_.IsAdic J :=
    (isIdealOfDefinition_iff_isAdic ⟨_, hLD⟩ J).1 hJdef
  obtain ⟨m, hm⟩ := hJadic.exists_pow_le hLD 1
  have hLDp : ¬ I.map (algebraMap A
      (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))) ≤ p := by
    intro hle
    exact hJp (Ideal.IsPrime.le_of_pow_le (le_trans (by simpa using hm) hle))
  -- transport the prime down and apply the base change for flatness
  let q : Ideal (B ⊗[A] C) := p.comap e.toRingHom
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have hLq : ¬ I.map (algebraMap A (B ⊗[A] C)) ≤ q := fun hle =>
    hLDp (Ideal.map_le_iff_le_comap.mpr (Ideal.map_le_iff_le_comap.mp hle :))
  have hq := flat_atPrime_tensorProduct_of_flat I hIdef hflat q hLq
  -- and transport the flatness back up
  refine flat_atPrime_of_ringEquiv_of_eq e.symm
    (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))) p q ?_ ?_
  · change p = (p.comap e.toRingHom).comap e.symm.toRingHom
    rw [Ideal.comap_comap, show (e.toRingHom.comp e.symm.toRingHom) = RingHom.id _ from
      RingHom.ext fun x => e.apply_symm_apply x, Ideal.comap_id]
  · have hcomp : e.symm.toRingHom.comp
        (algebraMap C (TopologicalRing.CompletedTensorProduct (R := A) (M := B) (N := C))) =
        algebraMap C (B ⊗[A] C) := RingHom.ext fun c => e.symm_apply_apply _
    rw [RingEquiv.toRingHom_eq_coe] at hcomp
    rwa [hcomp]

end Rig

end
