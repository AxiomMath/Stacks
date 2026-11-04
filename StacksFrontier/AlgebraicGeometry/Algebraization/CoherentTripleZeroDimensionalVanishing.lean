module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedFibreSupportTransfer
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedPointReduction
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleSectionPairAvoidance
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleZeroEuler
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleZeroSupport
public import StacksFrontier.AlgebraicGeometry.AssociatedPointPrime.Divisors
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.Basic
public import StacksFrontier.RingTheory.Depth.Ext
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# The closed-fibre member of a triple of zero-dimensional support vanishes

Let `T = (F, F₀, α)` be a coherent triple over a Noetherian local ring `A` with `f ∈ 𝔪`. If the
support of `F` has dimension at most `0`, then `f` vanishes at no point of `Supp F`, the inverse
image of `F` on the punctured closed fibre is zero, and `F₀` vanishes as soon as the closed point
of the closed fibre is not an associated point of it. This is the vanishing clause of the
induction step of [Stacks, Tag 0F27].

The dimension hypothesis cannot be weakened to `IsZero T.F`: for `A = k[[x, y]]`, `f = y`, `T`
the unit triple and `L` the invertible triple whose gluing is multiplication by `x`, the section
pair `σ = 1`, `σ₀ = x` leaves a cokernel triple `G` with `G.F = 0` and `G.F₀ = k[[x]]/x = k`.

## Main results

* `AlgebraicGeometry.IsAffineOpen.mem_primeIdealOf_iff_notMem_basicOpen`: a section lies in the
  prime of a point of an affine open exactly when the point is outside its nonvanishing locus.
* `Stacks.Algebraization.mem_asIdeal_morphismRestrict_closedImmersion`: `f` lies in the prime of
  every point of the punctured spectrum in the image of the punctured closed fibre.
* `Stacks.Algebraization.CoherentTriple.notMem_asIdeal_of_mem_supp_of_topologicalKrullDim_le`:
  `f` vanishes at no point of a zero-dimensional support.
* `Stacks.Algebraization.CoherentTriple.supp_pullback_eq_empty_of_topologicalKrullDim_le`: the
  inverse image of the punctured-spectrum member on the punctured closed fibre then has empty
  support.
* `Stacks.Algebraization.CoherentTriple.isZero_F₀_of_topologicalKrullDim_le`: the closed-fibre
  member of a coherent triple of zero-dimensional support vanishes, provided the closed point is
  not an associated point of it.
* `Stacks.Algebraization.CoherentTriple.isZero_F₀_quotientTriple_of_topologicalKrullDim_le`: the
  same for the quotient triple, with no condition at the closed point.
* `Stacks.Algebraization.CoherentTriple.isZero_F₀_of_shortExact_twistZ`: the closed-fibre member
  of the quotient in a twisted short exact sequence vanishes when that of the triple being
  twisted does.
* `CoherentTriple.eulerCharacteristic_eq_zero_of_shortExact_twistZ_quotientTriple`: the Euler
  characteristic of the quotient in a twisted short exact sequence of quotient triples vanishes
  when the support is zero-dimensional and the punctured-spectrum member of the quotient is zero.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 05AH](https://stacks.math.columbia.edu/tag/05AH)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace
open Stacks.AlgebraicGeometry.AssociatedPointPrime

universe u

/-! ### Membership in the prime of a point of an affine open -/

namespace AlgebraicGeometry

/-- A section lies in the prime of a point of an affine open exactly when the point is outside
its nonvanishing locus. -/
public theorem IsAffineOpen.mem_primeIdealOf_iff_notMem_basicOpen {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) (s : Γ(X, U)) :
    s ∈ (hU.primeIdealOf x).asIdeal ↔ (x : X) ∉ X.basicOpen s := by
  have key : (x : X) ∈ X.basicOpen s ↔ s ∉ (hU.primeIdealOf x).asIdeal := by
    rw [← PrimeSpectrum.mem_basicOpen s (hU.primeIdealOf x),
      ← hU.fromSpec_preimage_basicOpen s]
    exact (congrArg (· ∈ X.basicOpen s) (hU.fromSpec_primeIdealOf x).symm).to_iff
  rw [key, not_not]

end AlgebraicGeometry

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}

/-! ### The punctured closed fibre lies over the zero locus of `f` -/

omit [IsNoetherianRing A] in
/-- `f` lies in the prime of every point of the punctured spectrum coming from the punctured
closed fibre. -/
public theorem mem_asIdeal_morphismRestrict_closedImmersion
    (y : (puncturedClosedFibre A f).toScheme) :
    f ∈ (show (Stacks.Divisors.puncturedSpectrum A).toScheme from
      (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A)).base y).1.asIdeal := by
  have h : (Stacks.Divisors.puncturedSpectrum A).ι.base
      ((morphismRestrict (closedImmersion A f) (Stacks.Divisors.puncturedSpectrum A)).base y) =
      (closedImmersion A f).base ((puncturedClosedFibre A f).ι.base y) := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
    rfl
  simp only at h
  rw [show (show (Stacks.Divisors.puncturedSpectrum A).toScheme from
      (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A)).base y).1 = _ from h]
  show (Ideal.Quotient.mk (Ideal.span {f})) f ∈
    ((puncturedClosedFibre A f).ι.base y).asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self f)]
  exact Ideal.zero_mem _

/-! ### `f` vanishes at no point of a zero-dimensional support -/

/-- If the support of the punctured-spectrum member of a coherent triple has dimension at most
`0`, then `f` lies in the prime of no point of that support. -/
public theorem CoherentTriple.notMem_asIdeal_of_mem_supp_of_topologicalKrullDim_le
    (T : CoherentTriple A f)
    (hdim : topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞))
    {x : (Stacks.Divisors.puncturedSpectrum A).toScheme} (hx : x ∈ SheafOfModules.supp T.F) :
    f ∉ x.1.asIdeal := by
  have : IsLocallyNoetherian (Stacks.Divisors.puncturedSpectrum A).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (Stacks.Divisors.puncturedSpectrum A).ι
  have := T.coherent_F
  have : T.F.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have hmin : ∀ y : (Stacks.Divisors.puncturedSpectrum A).toScheme,
      y ∈ SheafOfModules.supp T.F → y ⤳ x → y = x := by
    intro y hy hyx
    have h0 : topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ 0 := by simpa using hdim
    have heq : (⟨y, hy⟩ : ↥(SheafOfModules.supp T.F)) = ⟨x, hx⟩ :=
      Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero h0
        (Topology.IsInducing.subtypeVal.specializes_iff.1 hyx)
    exact congrArg Subtype.val heq
  have hass : Stacks.Divisors.IsAssociatedPoint T.F x :=
    mem_associatedPoints_of_mem_supp_of_specialization _ T.F x hx hmin
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := (Stacks.Divisors.puncturedSpectrum A).toScheme) (U := (⊤ : _)) (x := x) trivial
  have : IsNoetherianRing Γ((Stacks.Divisors.puncturedSpectrum A).toScheme, W) :=
    IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hprime := (divisorsIsAssociatedPoint_iff_mem_associatedPrimes T.F hW hxW).1 hass
  have hnot := (isSMulRegular_iff_forall_notMem_associatedPrimes _).1 (T.torsionFree W) _ hprime
  rw [hW.mem_primeIdealOf_iff_notMem_basicOpen ⟨x, hxW⟩, not_not] at hnot
  have hglob : scalarOnOpen A f W =
      (Stacks.Divisors.puncturedSpectrum A).toScheme.presheaf.map
        (homOfLE (le_top : W ≤ ⊤)).op (puncturedScalars A f) := rfl
  rw [hglob, Scheme.basicOpen_res] at hnot
  exact (mem_basicOpen_puncturedScalars A f x).1 hnot.2

/-! ### The closed-fibre member vanishes -/

/-- The inverse image of the punctured-spectrum member of a coherent triple on the punctured
closed fibre has empty support, as soon as the support of that member has dimension at most
`0`. -/
public theorem CoherentTriple.supp_pullback_eq_empty_of_topologicalKrullDim_le
    (T : CoherentTriple A f)
    (hdim : topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞)) :
    SheafOfModules.supp ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A))).obj T.F) = ∅ := by
  have := T.coherent_F
  have := _root_.SheafOfModules.IsCoherent.isFiniteType (M := T.F)
  rw [SheafOfModules.supp_pullback]
  refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
  exact T.notMem_asIdeal_of_mem_supp_of_topologicalKrullDim_le hdim hy
    (mem_asIdeal_morphismRestrict_closedImmersion y)

/-- The closed-fibre member of a coherent triple whose punctured-spectrum member has
zero-dimensional support vanishes, provided the closed point of the closed fibre is not an
associated point of it. -/
public theorem CoherentTriple.isZero_F₀_of_topologicalKrullDim_le
    [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f)
    (hdim : topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞))
    (hass : ¬ Stacks.Divisors.IsAssociatedPoint T.F₀
      (IsLocalRing.closedPoint (A ⧸ Ideal.span {f}))) :
    IsZero T.F₀ :=
  T.isZero_F₀_of_isEmpty hf (T.supp_pullback_eq_empty_of_topologicalKrullDim_le hdim) hass

/-- The closed-fibre member of the quotient triple `T.quotientTriple hf` vanishes as soon as the
support of its punctured-spectrum member has dimension at most `0`. -/
public theorem CoherentTriple.isZero_F₀_quotientTriple_of_topologicalKrullDim_le
    [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A) (T : CoherentTriple A f)
    (hdim : topologicalKrullDim ↥(SheafOfModules.supp (T.quotientTriple hf).F) ≤
      ((0 : ℕ) : WithBot ℕ∞)) :
    IsZero (T.quotientTriple hf).F₀ :=
  CoherentTriple.isZero_F₀_of_topologicalKrullDim_le hf (T.quotientTriple hf) hdim
    (T.not_isAssociatedPoint_closedPoint_quotientTriple hf)

/-! ### The vanishing clause, for the quotient the twisted sequence produces -/

omit [IsNoetherianRing A] in
/-- In a short exact sequence of twists `T(n) → T(n + 1) → G(n)`, the closed-fibre member of `G`
vanishes as soon as the closed-fibre member of `T` does. -/
public theorem CoherentTriple.isZero_F₀_of_shortExact_twistZ (hf : f ∈ maximalIdeal A)
    {T G L : CoherentTriple A f} (hL : IsInvertibleTriple L) {n : ℤ}
    {u : (T.twistZ L hL n).Hom (T.twistZ L hL (n + 1))}
    {v : (T.twistZ L hL (n + 1)).Hom (G.twistZ L hL n)}
    (hse : CoherentTriple.ShortExact u v) (hT₀ : IsZero T.F₀) :
    IsZero G.F₀ := by
  have hmid : IsZero ((T.twistZ L hL (n + 1)).F₀) :=
    IsZero.of_iso hT₀ (T.twistZF₀Iso hf L hL (n + 1))
  have := hse.closedFibre.epi_g
  have htw : IsZero ((G.twistZ L hL n).F₀) :=
    (IsZero.iff_id_eq_zero _).2 ((cancel_epi v.onClosedFibre).1 (hmid.eq_of_src _ _))
  exact IsZero.of_iso htw (G.twistZF₀Iso hf L hL n).symm

/-- **The vanishing clause of the induction step of [Stacks, Tag 0F27].** Let
`T' = T.quotientTriple hf`. In a short exact sequence of twists `T'(n) → T'(n + 1) → G(n)`, if
the support of `T.F` has dimension at most `0` and `G.F` is zero, then the Euler characteristic
of `G` is `0`. -/
public theorem CoherentTriple.eulerCharacteristic_eq_zero_of_shortExact_twistZ_quotientTriple
    [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A) (hreg : IsRegular f)
    (T : CoherentTriple A f) {G L : CoherentTriple A f} (hL : IsInvertibleTriple L) {n : ℤ}
    {u : (((T.quotientTriple hf).twistZ L hL n)).Hom ((T.quotientTriple hf).twistZ L hL (n + 1))}
    {v : (((T.quotientTriple hf).twistZ L hL (n + 1))).Hom (G.twistZ L hL n)}
    (hse : CoherentTriple.ShortExact u v)
    (hdim : topologicalKrullDim ↥(SheafOfModules.supp T.F) ≤ ((0 : ℕ) : WithBot ℕ∞))
    (hG : IsZero G.F) :
    G.eulerCharacteristic hf hreg = 0 :=
  CoherentTriple.eulerCharacteristic_eq_zero_of_isZero hf hreg hG
    (CoherentTriple.isZero_F₀_of_shortExact_twistZ hf hL hse
      (CoherentTriple.isZero_F₀_quotientTriple_of_topologicalKrullDim_le hf T hdim))

end Stacks.Algebraization

end
