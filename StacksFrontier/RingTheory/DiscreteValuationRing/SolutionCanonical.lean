module

public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureBaseChangeConstruction
public import StacksFrontier.RingTheory.FormallySmooth.AdicArrowIso

/-!
# The canonical base-change package inherits the solution property

`AlgebraicGeometry.IsSolutionForStalk` asserts that *some*
`IsDiscreteValuationRing.IntegralClosureBaseChange` package is a solution, and the structure
deliberately does not fix carrier types: all that is known of its three rings is that `A₁` and
`B₁` are integral closures and that `L₁` is identified with the reduction of `L ⊗[K] K₁` by the
field `eL₁`.  Anything reading a solution off a *named* ring — the integral closure appearing in
the identification of the local rings of a normalized base change, say — therefore has to move
the solution property from the package it is handed to the canonical one,
`IsDiscreteValuationRing.canonicalBaseChange`, whose carriers are literally
`integralClosure A K₁` and `integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))`.

**That transport is carried out here.**  Uniqueness of integral closures identifies `D.A₁` with
`integralClosure A K₁` over `A` and, after `eL₁` has been seen to be an isomorphism of
`B`-algebras, `D.B₁` with `integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))` over `B`;
the field `ringSquare` of the package says exactly that the two identifications commute with the
two maps `A₁ → B₁`.  Adic formal smoothness depends only on the isomorphism class of an arrow, so
the formal smoothness of every `(D.A₁)_p → (D.B₁)_q` becomes that of the corresponding
localization of the canonical package.

## Main results

* `IsDiscreteValuationRing.IntegralClosureBaseChange.algEquivIntegralClosureFractionField`: the
  `A`-algebra isomorphism `D.A₁ ≃ integralClosure A K₁`.
* `IsDiscreteValuationRing.IntegralClosureBaseChange.algEquivIntegralClosureReducedCompositum`:
  the `B`-algebra isomorphism
  `D.B₁ ≃ integralClosure B ((L ⊗[K] K₁) ⧸ nilradical (L ⊗[K] K₁))`.
* `IsDiscreteValuationRing.IntegralClosureBaseChange.isSolution_canonicalBaseChange`: if `D` is a
  solution, so is `IsDiscreteValuationRing.canonicalBaseChange`.

## Implementation notes

The twenty-two instance fields of `IsDiscreteValuationRing.IntegralClosureBaseChange` are
instance-implicit *fields*, not instances, so each statement about `D.L₁`, `D.A₁` or `D.B₁` would
otherwise have to introduce them by hand.  They are switched on as `local instance`s for this
file instead; nothing leaks to consumers.

## References

* [Stacks Project, Tag 09EM](https://stacks.math.columbia.edu/tag/09EM)
* [Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

@[expose] public section

open scoped TensorProduct

universe uA uB uK uL uK₁ uL₁ uA₁ uB₁ v

/-! ### Localizations at a prime along a ring isomorphism -/

/-- A ring isomorphism carries the complement of the contraction of a prime to the complement of
that prime. -/
theorem Submonoid.map_primeCompl_of_ringEquiv {R : Type uA₁} {R' : Type uB₁}
    [CommRing R] [CommRing R'] (e : R ≃+* R') {p : Ideal R} [p.IsPrime] {q : Ideal R'}
    [q.IsPrime] (hpq : p = q.comap (e : R →+* R')) :
    p.primeCompl.map e.toMonoidHom = q.primeCompl := by
  ext z
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
  refine ⟨?_, fun hz => ⟨e.symm z, ?_, e.apply_symm_apply z⟩⟩
  · rintro ⟨a, ha, rfl⟩
    rwa [hpq, Ideal.mem_comap] at ha
  · rw [hpq, Ideal.mem_comap]
    simpa using hz

/-- **A ring isomorphism identifies the localizations at corresponding primes.**  If `p` is the
contraction of `q` along `e : R ≃+* R'`, then `e` induces an isomorphism `R_p ≃ R'_q` carrying
the image of `a` to the image of `e a`. -/
noncomputable def localizationAtPrimeRingEquivOfRingEquiv {R : Type uA₁} {R' : Type uB₁}
    [CommRing R] [CommRing R'] (e : R ≃+* R') {p : Ideal R} [p.IsPrime] {q : Ideal R'}
    [q.IsPrime] (hpq : p = q.comap (e : R →+* R')) :
    Localization.AtPrime p ≃+* Localization.AtPrime q :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p) (Localization.AtPrime q) e
    (Submonoid.map_primeCompl_of_ringEquiv e hpq)

/-- The isomorphism `localizationAtPrimeRingEquivOfRingEquiv e hpq` sends the image of `a` in
`R_p` to the image of `e a` in `R'_q`. -/
@[simp]
theorem localizationAtPrimeRingEquivOfRingEquiv_apply {R : Type uA₁} {R' : Type uB₁}
    [CommRing R] [CommRing R'] (e : R ≃+* R') {p : Ideal R} [p.IsPrime] {q : Ideal R'}
    [q.IsPrime] (hpq : p = q.comap (e : R →+* R')) (a : R) :
    localizationAtPrimeRingEquivOfRingEquiv e hpq (algebraMap R (Localization.AtPrime p) a) =
      algebraMap R' (Localization.AtPrime q) (e a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (Submonoid.map_primeCompl_of_ringEquiv e hpq) a

namespace IsDiscreteValuationRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra isScalarTower_tensor_of_base
  algebraIntegralClosure isScalarTower_integralClosure

namespace IntegralClosureBaseChange

attribute [local instance] IntegralClosureBaseChange.commRingL₁
  IntegralClosureBaseChange.commRingA₁ IntegralClosureBaseChange.commRingB₁
  IntegralClosureBaseChange.algebraKL₁ IntegralClosureBaseChange.algebraLL₁
  IntegralClosureBaseChange.algebraK₁L₁ IntegralClosureBaseChange.algebraBL₁
  IntegralClosureBaseChange.algebraAA₁ IntegralClosureBaseChange.algebraA₁K₁
  IntegralClosureBaseChange.algebraBB₁ IntegralClosureBaseChange.algebraB₁L₁
  IntegralClosureBaseChange.algebraAB₁ IntegralClosureBaseChange.algebraA₁B₁
  IntegralClosureBaseChange.isScalarTowerKLL₁ IntegralClosureBaseChange.isScalarTowerKK₁L₁
  IntegralClosureBaseChange.isScalarTowerBLL₁ IntegralClosureBaseChange.isScalarTowerAA₁K₁
  IntegralClosureBaseChange.isScalarTowerBB₁L₁ IntegralClosureBaseChange.isScalarTowerABB₁
  IntegralClosureBaseChange.isScalarTowerAA₁B₁ IntegralClosureBaseChange.isIntegralClosureA₁
  IntegralClosureBaseChange.isIntegralClosureB₁

variable {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL} {K₁ : Type uK₁}
    [CommRing A] [CommRing B] [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L] [Module.Finite K K₁]
    (D : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁} A B K L K₁)

/-! ### The identification of `L₁` over `B` -/

/-- **`eL₁` is an isomorphism of `B`-algebras.**  It is only recorded as `K`-linear, but the
structure map of `B` into `L₁` factors through `L`, on which `eL₁_left` pins `eL₁` down. -/
theorem eL₁_algebraMap_eq (b : B) :
    D.eL₁ (algebraMap B D.L₁ b) = algebraMap B (reducedCompositum K L K₁) b := by
  rw [IsScalarTower.algebraMap_apply B L D.L₁, D.eL₁_left]
  rfl

/-- The identification of `L₁` with the reduced compositum, as an isomorphism of `B`-algebras. -/
noncomputable def algEquivReducedCompositum : D.L₁ ≃ₐ[B] reducedCompositum K L K₁ :=
  AlgEquiv.ofRingEquiv (f := D.eL₁.toRingEquiv) D.eL₁_algebraMap_eq

/-- `algEquivReducedCompositum` agrees with `eL₁` as a function. -/
@[simp]
theorem algEquivReducedCompositum_apply (x : D.L₁) :
    D.algEquivReducedCompositum x = D.eL₁ x := rfl

/-! ### The two integral closures -/

/-- **`D.A₁` is the integral closure of `A` in `K₁`.**  Both are integral closures of `A` in
`K₁`, and integral closures are unique. -/
noncomputable def algEquivIntegralClosureFractionField : D.A₁ ≃ₐ[A] integralClosure A K₁ :=
  IsIntegralClosure.equiv A D.A₁ K₁ (integralClosure A K₁)

/-- The image of `x : D.A₁` under `algEquivIntegralClosureFractionField`, viewed in `K₁`, is the
image of `x` under the structure map `D.A₁ → K₁`. -/
@[simp]
theorem coe_algEquivIntegralClosureFractionField (x : D.A₁) :
    (D.algEquivIntegralClosureFractionField x : K₁) = algebraMap D.A₁ K₁ x :=
  IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ (integralClosure A K₁) x

/-- **`D.B₁` is the integral closure of `B` in the reduced compositum.**  It is the integral
closure of `B` in `D.L₁`, by uniqueness of integral closures, and `eL₁` carries that over. -/
noncomputable def algEquivIntegralClosureReducedCompositum :
    D.B₁ ≃ₐ[B] integralClosure B (reducedCompositum K L K₁) :=
  (IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)).trans
    D.algEquivReducedCompositum.mapIntegralClosure

/-- The image of `x : D.B₁` under `algEquivIntegralClosureReducedCompositum`, viewed in the
reduced compositum, is `eL₁` applied to the image of `x` in `D.L₁`. -/
@[simp]
theorem coe_algEquivIntegralClosureReducedCompositum (x : D.B₁) :
    (D.algEquivIntegralClosureReducedCompositum x : reducedCompositum K L K₁) =
      D.eL₁ (algebraMap D.B₁ D.L₁ x) := by
  rw [algEquivIntegralClosureReducedCompositum, AlgEquiv.trans_apply,
    AlgEquiv.coe_mapIntegralClosure, algEquivReducedCompositum_apply]
  exact congrArg D.eL₁ (IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁ (integralClosure B D.L₁) x)

/-- **The two identifications commute with the two maps between the integral closures.**  This is
the field `ringSquare` of the package, read through `eL₁`. -/
theorem algebraMap_algEquivIntegralClosure (x : D.A₁) :
    algebraMap ↥(integralClosure A K₁) ↥(integralClosure B (reducedCompositum K L K₁))
        (D.algEquivIntegralClosureFractionField x) =
      D.algEquivIntegralClosureReducedCompositum (algebraMap D.A₁ D.B₁ x) := by
  apply Subtype.ext
  rw [coe_algEquivIntegralClosureReducedCompositum, D.ringSquare, D.eL₁_right,
    (integralClosureCompositumMap A B K L K₁).algebraMap_toAlgebra,
    coe_integralClosureCompositumMap, coe_algEquivIntegralClosureFractionField]
  rfl

/-! ### The solution property -/

/-- **The canonical base-change package is a solution as soon as some package is.**  The two
identifications of integral closures carry each localization of `D` to the corresponding
localization of `IsDiscreteValuationRing.canonicalBaseChange`, and adic formal smoothness depends
only on the isomorphism class of the arrow. -/
theorem isSolution_canonicalBaseChange
    (hD : D.IsSolution.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁, v}) :
    (canonicalBaseChange A B K L K₁).IsSolution.{uA, uB, uK, uL, uK₁, max uL uK₁, uK₁,
      max uL uK₁, v} := by
  intro q' hq'
  have _ : q'.IsPrime := hq'.isPrime
  let eA : D.A₁ ≃+* (canonicalBaseChange A B K L K₁).A₁ :=
    D.algEquivIntegralClosureFractionField.toRingEquiv
  let eB : D.B₁ ≃+* (canonicalBaseChange A B K L K₁).B₁ :=
    D.algEquivIntegralClosureReducedCompositum.toRingEquiv
  have hsq : ∀ x : D.A₁, algebraMap (canonicalBaseChange A B K L K₁).A₁
      (canonicalBaseChange A B K L K₁).B₁ (eA x) =
      eB (algebraMap D.A₁ D.B₁ x) := D.algebraMap_algEquivIntegralClosure
  have hqmax : (q'.comap (eB : D.B₁ →+* (canonicalBaseChange A B K L K₁).B₁)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective
      (f := (eB : D.B₁ →+* (canonicalBaseChange A B K L K₁).B₁))
      (fun y => ⟨eB.symm y, eB.apply_symm_apply y⟩) (H := hq')
  have _ : (q'.comap (eB : D.B₁ →+* (canonicalBaseChange A B K L K₁).B₁)).IsPrime :=
    hqmax.isPrime
  have _ : ((q'.comap (eB : D.B₁ →+* (canonicalBaseChange A B K L K₁).B₁)).comap
    (algebraMap D.A₁ D.B₁)).IsPrime := Ideal.IsPrime.comap _
  have _ : (q'.comap (algebraMap (canonicalBaseChange A B K L K₁).A₁
      (canonicalBaseChange A B K L K₁).B₁)).IsPrime := Ideal.IsPrime.comap _
  have hpp' : (q'.comap (eB : D.B₁ →+* (canonicalBaseChange A B K L K₁).B₁)).comap
        (algebraMap D.A₁ D.B₁) =
      (q'.comap (algebraMap (canonicalBaseChange A B K L K₁).A₁
        (canonicalBaseChange A B K L K₁).B₁)).comap
          (eA : D.A₁ →+* (canonicalBaseChange A B K L K₁).A₁) := by
    rw [Ideal.comap_comap, Ideal.comap_comap]
    exact congrArg q'.comap (RingHom.ext fun x => (hsq x).symm)
  refine RingHom.FormallySmoothNAdic.of_arrowEquiv_of_map_eq
    (localizationAtPrimeRingEquivOfRingEquiv eA hpp')
    (localizationAtPrimeRingEquivOfRingEquiv eB rfl) ?_
    (IsLocalRing.map_ringEquiv_maximalIdeal _) (hD _ hqmax)
  refine IsLocalization.ringHom_ext
    ((q'.comap (eB : D.B₁ →+* (canonicalBaseChange A B K L K₁).B₁)).comap
      (algebraMap D.A₁ D.B₁)).primeCompl
    (RingHom.ext fun a => ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, localizationAtPrimeRingEquivOfRingEquiv_apply,
    Localization.localRingHom_to_map]
  exact congrArg (algebraMap _ (Localization.AtPrime q')) (hsq a)

end IntegralClosureBaseChange

end IsDiscreteValuationRing

end
