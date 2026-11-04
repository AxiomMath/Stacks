module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.BadLocusComplement
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.CoherentCyclePresentation

/-!
# Part (4) of Stacks 02SW: the equality of cycles

In the situation of [Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW) — `X` locally of
finite type over the base of a Chow situation with `dim_δ(X) ≤ k + 1` and no embedded points, `ℱ`
coherent of full support with no embedded associated points, `ℒ` invertible and `s` a regular
meromorphic section of `ℒ` — part (4) reads

  `[𝒬₂]_k - [𝒬₁]_k = ∑ᵢ mᵢ (Xᵢ → X)_* div_{ℒ|_{Xᵢ}}(sᵢ)`   in   `Z_k(X)`,

where `[ℱ]_{k+1} = ∑ᵢ mᵢ [Xᵢ]` presents the cycle of `ℱ` in delta-dimension `k + 1`.

## Main definitions

* `Stacks.Chow.denominatorQuotientCycle` and `Stacks.Chow.denominatorSectionQuotientCycle` — the
  two cycles `[𝒬₁]_k` and `[𝒬₂]_k`, built from parts (1) and (2) of the tag.
* `Stacks.Chow.componentDivisorCoefficient` — the coefficient of
  `(Xη → X)_* div_{ℒ|_{Xη}}(sη)`, as a function of `η` defined on all of `X`, with junk value
  zero where `η` is not the generic point of a component of delta-dimension `k + 1`.

## Main results

* `Stacks.Chow.mem_genericPoints_of_relativeDimension_eq` — on a scheme of delta-dimension at
  most `k + 1` a point of delta-dimension `k + 1` is the generic point of an irreducible
  component.
* `Stacks.Chow.stalkIdeal_integralComponentAt_mem_minimalPrimes` — the ideal sheaf of an
  irreducible component through `ξ` cuts out a minimal prime of `𝒪_{X, ξ}`.
* `Stacks.Chow.componentDivisorCoefficient_eq` — the characterization of the coefficient.
* `Stacks.Chow.denominatorQuotients_cycle_sub_apply_eq_finsum` — **part (4)**.

## Implementation notes

The identity is stated coefficientwise, at an arbitrary point `x` of `X`. That is what makes the
right-hand side meaningful without a finiteness hypothesis on `X`: the family of components of
delta-dimension `k + 1` is locally finite but not finite, so the cycle `∑ᵢ mᵢ (Xᵢ → X)_* div(sᵢ)`
exists as a locally finite sum rather than as a finite one, and at each point only finitely many
summands are nonzero. The index set is the one `[ℱ]_{k+1} = ∑ᵢ mᵢ [Xᵢ]` is presented over by
`Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_eq_finsum`, namely the set cut out by the
predicate of `Stacks.Chow.topSupportPoints C f ℱ (k + 1)`, so the multiplicities are literally
the `mᵢ`. With `ℱ` of full support those points are exactly the generic points of the
irreducible components of `X` of delta-dimension `k + 1`, which is how part (4) names them:
`Stacks.Chow.mem_genericPoints_of_relativeDimension_eq` is that identification, and it is what
makes each summand meaningful.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Order Topology
open TopologicalSpace
open Stacks.DenominatorIdeal (sectionMap toK)

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### Top-dimensional points are generic points -/

/-- **On a scheme of delta-dimension at most `k + 1` a point of delta-dimension `k + 1` is the
generic point of an irreducible component.** -/
theorem mem_genericPoints_of_relativeDimension_eq (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt)) {η : X}
    (hδ : relativeDimension C.dimensionFunction f η = k + 1) : η ∈ genericPoints X := by
  refine mem_genericPoints_of_isMax fun y hy => ?_
  by_contra hne
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction f
  have hlt : η < y := lt_iff_le_not_ge.mpr ⟨hy, hne⟩
  have hstrict := d.strictAnti_specializes hlt.le hlt.ne'
  have hb := StalkLocalSituation.relativeDimension_le_of_schemeDeltaDimension_le C f hdim y
  rw [hd η, hd y, hδ] at hstrict
  omega

/-! ### The minimal prime a component cuts out -/

/-- **The ideal sheaf of an irreducible component through `ξ` cuts out a minimal prime of
`𝒪_{X, ξ}`.** -/
theorem stalkIdeal_integralComponentAt_mem_minimalPrimes [IsLocallyNoetherian X] {ξ η : X}
    (hη : η ∈ genericPoints X) (hspec : η ⤳ ξ) :
    (integralComponentAt η).stalkIdeal ξ ∈ minimalPrimes (X.presheaf.stalk ξ) := by
  have hηmax : IsMax η := isMax_of_mem_genericPoints ⟨η, hη⟩
  obtain ⟨q, hq, hqη⟩ := (bijOn_fromSpecStalk_minimalPrimes_bot ξ).surjOn
    ⟨hspec, fun η' hb => (Specializes.antisymm hb (hηmax hb)).eq⟩
  have hstalk : (integralComponentAt (X.fromSpecStalk ξ q)).stalkIdeal ξ = q.asIdeal :=
    stalkIdeal_vanishingIdeal_closure_fromSpecStalk ξ q
  rw [← hqη, hstalk]
  exact hq

/-! ### The coefficient of the component divisor as a function of the component -/

open scoped Classical in
/-- **The coefficient of `(Xη → X)_* div_{ℒ|_{Xη}}(sη)` at a point**, as a function of `η` defined
on all of `X`: the junk value is zero where `η` is not the generic point of an irreducible
component of delta-dimension `k + 1`. -/
def componentDivisorCoefficient (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L : X.Modules) (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) (k : ℤ) (η x : X) : ℤ :=
  if h : η ∈ genericPoints X ∧ relativeDimension C.dimensionFunction f η = k + 1 then
    (componentDivisorCycle C f L s hL hs h.1 h.2).1 x
  else 0

/-- **The characterization of `Stacks.Chow.componentDivisorCoefficient`.** -/
theorem componentDivisorCoefficient_eq (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (L : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) {k : ℤ} {η : X}
    (hη : η ∈ genericPoints X)
    (hδη : relativeDimension C.dimensionFunction f η = k + 1) (x : X) :
    componentDivisorCoefficient C f L s hL hs k η x =
      (componentDivisorCycle C f L s hL hs hη hδη).1 x := by
  unfold componentDivisorCoefficient
  exact dite_eq_left ⟨hη, hδη⟩

/-- The coefficient vanishes at a point outside the component. -/
theorem componentDivisorCoefficient_eq_zero_of_not_specializes (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (L : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) (k : ℤ) (η : X) {x : X}
    (hx : ¬ η ⤳ x) : componentDivisorCoefficient C f L s hL hs k η x = 0 := by
  unfold componentDivisorCoefficient
  split_ifs with h
  · refine componentDivisorCycle_apply_eq_zero_of_notMem_range C f L s hL hs h.1 h.2 ?_
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
    exact fun hmem => hx (specializes_iff_mem_closure.mpr hmem)
  · rfl

/-! ### The two quotient cycles -/

variable (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f] (L F : X.Modules)
  (s : AlgebraicGeometry.MeromorphicSection X.sheaf L) [F.IsCoherent] {k : ℤ}
  (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
  (hX : HasNoEmbeddedPoints X)
  (hF : HasNoEmbeddedAssociatedPoints F)
  (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
  (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
  (hs : IsRegularMeromorphicSection X.sheaf L s)

/-- **The cycle `[𝒬₁]_k`** of the first denominator quotient of [Stacks, Tag 02SW]: it is
coherent by part (2) of the tag and supported in delta-dimension at most `k`, so it has a cycle
in `Z_k(X)` by [Stacks, Tag 02QX]. -/
def denominatorQuotientCycle : CycleGroup C f k :=
  letI := isCoherent_denominatorQuotient C f L F s hdim hX hF hSupp hL hs
  cycleAssociatedToCoherentSheaf C f (denominatorQuotientDecl L F s) k
    (schemeDeltaDimension_denominatorQuotient_le C f L F s hdim hX hF hSupp hL hs)

/-- **The cycle `[𝒬₂]_k`** of the second denominator quotient of [Stacks, Tag 02SW]. -/
def denominatorSectionQuotientCycle : CycleGroup C f k :=
  letI := LocallyOfFiniteType.isLocallyNoetherian f
  letI := isCoherent_denominatorSectionQuotient C f L F s hdim hX hF hSupp hL hs
  cycleAssociatedToCoherentSheaf C f
    (DenominatorStalk.denominatorSectionQuotientDecl L F s hL hs hF hSupp) k
    (schemeDeltaDimension_denominatorSectionQuotient_le C f L F s hdim hX hF hSupp hL hs)

/-- The coefficient of `[𝒬₁]_k` at a point of delta-dimension `k` is the multiplicity of the
quotient there. -/
theorem denominatorQuotientCycle_apply_of_relativeDimension_eq {x : X}
    (hx : relativeDimension C.dimensionFunction f x = k) :
    (denominatorQuotientCycle C f L F s hdim hX hF hSupp hL hs).1 x =
      sheafMultiplicity (denominatorQuotientDecl L F s) x :=
  let := isCoherent_denominatorQuotient C f L F s hdim hX hF hSupp hL hs
  cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f
    (denominatorQuotientDecl L F s) k
    (schemeDeltaDimension_denominatorQuotient_le C f L F s hdim hX hF hSupp hL hs) hx

/-- The coefficient of `[𝒬₁]_k` vanishes at a point whose delta-dimension is not `k`. -/
theorem denominatorQuotientCycle_apply_of_relativeDimension_ne {x : X}
    (hx : relativeDimension C.dimensionFunction f x ≠ k) :
    (denominatorQuotientCycle C f L F s hdim hX hF hSupp hL hs).1 x = 0 :=
  let := isCoherent_denominatorQuotient C f L F s hdim hX hF hSupp hL hs
  cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f
    (denominatorQuotientDecl L F s) k
    (schemeDeltaDimension_denominatorQuotient_le C f L F s hdim hX hF hSupp hL hs) hx

/-- The coefficient of `[𝒬₂]_k` at a point of delta-dimension `k` is the multiplicity of the
quotient there. -/
theorem denominatorSectionQuotientCycle_apply_of_relativeDimension_eq {x : X}
    (hx : relativeDimension C.dimensionFunction f x = k) :
    (denominatorSectionQuotientCycle C f L F s hdim hX hF hSupp hL hs).1 x =
      sheafMultiplicity
        (@DenominatorStalk.denominatorSectionQuotientDecl X L F s
          (LocallyOfFiniteType.isLocallyNoetherian f) hL hs inferInstance hF hSupp) x :=
  let := LocallyOfFiniteType.isLocallyNoetherian f
  let := isCoherent_denominatorSectionQuotient C f L F s hdim hX hF hSupp hL hs
  cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_eq C f
    (DenominatorStalk.denominatorSectionQuotientDecl L F s hL hs hF hSupp) k
    (schemeDeltaDimension_denominatorSectionQuotient_le C f L F s hdim hX hF hSupp hL hs) hx

/-- The coefficient of `[𝒬₂]_k` vanishes at a point whose delta-dimension is not `k`. -/
theorem denominatorSectionQuotientCycle_apply_of_relativeDimension_ne {x : X}
    (hx : relativeDimension C.dimensionFunction f x ≠ k) :
    (denominatorSectionQuotientCycle C f L F s hdim hX hF hSupp hL hs).1 x = 0 :=
  let := LocallyOfFiniteType.isLocallyNoetherian f
  let := isCoherent_denominatorSectionQuotient C f L F s hdim hX hF hSupp hL hs
  cycleAssociatedToCoherentSheaf_apply_of_relativeDimension_ne C f
    (DenominatorStalk.denominatorSectionQuotientDecl L F s hL hs hF hSupp) k
    (schemeDeltaDimension_denominatorSectionQuotient_le C f L F s hdim hX hF hSupp hL hs) hx

/-! ### Part (4) -/

/-- **Part (4) of [Stacks, Tag 02SW], the equality of cycles.** With `[ℱ]_{k+1} = ∑ᵢ mᵢ [Xᵢ]`,

  `[𝒬₂]_k - [𝒬₁]_k = ∑ᵢ mᵢ (Xᵢ → X)_* div_{ℒ|_{Xᵢ}}(sᵢ)`   in   `Z_k(X)`,

read coefficientwise at an arbitrary point `x` of `X` so that the right-hand side is the locally
finite sum the source asserts rather than a finite one; see the implementation notes. The index
set is the one over which `Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_eq_finsum` presents
`[ℱ]_{k+1}`, so the coefficients are literally its multiplicities. -/
theorem denominatorQuotients_cycle_sub_apply_eq_finsum (x : X) :
    (denominatorSectionQuotientCycle C f L F s hdim hX hF hSupp hL hs).1 x -
        (denominatorQuotientCycle C f L F s hdim hX hF hSupp hL hs).1 x =
      ∑ᶠ η ∈ {η : X | η ∈ SheafOfModules.supp F ∧
          relativeDimension C.dimensionFunction f η = k + 1},
        sheafMultiplicity F η * componentDivisorCoefficient C f L s hL hs k η x := by
  classical
  have hNoeth := LocallyOfFiniteType.isLocallyNoetherian f
  have hsum : ∑ᶠ η ∈ {η : X | η ∈ SheafOfModules.supp F ∧
          relativeDimension C.dimensionFunction f η = k + 1},
        sheafMultiplicity F η * componentDivisorCoefficient C f L s hL hs k η x =
      ∑ᶠ η ∈ {η : X | η ∈ SheafOfModules.supp F ∧ η ⤳ x ∧
          relativeDimension C.dimensionFunction f η = k + 1},
        sheafMultiplicity F η * componentDivisorCoefficient C f L s hL hs k η x := by
    refine finsum_mem_inter_support_eq' _ _ _ fun η hη => ?_
    have hspec : η ⤳ x := by
      by_contra hc
      exact hη (mul_eq_zero_of_right _
        (componentDivisorCoefficient_eq_zero_of_not_specializes C f L s hL hs k η hc))
    exact ⟨fun h => ⟨h.1, hspec, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  rw [hsum]
  by_cases hδ : relativeDimension C.dimensionFunction f x = k
  · by_cases hx : x ∈ denominatorBadLocus X L s
    · obtain ⟨V, hxV, hVaff, a, b, e, hbas, hbt, ha, hb, hid⟩ :=
        exists_affineOpen_sectionRatio_sheafMultiplicity_sub_eq_finsum_componentOrd C f L F s
          hdim hX hF hSupp hL hs hx hδ
      rw [denominatorSectionQuotientCycle_apply_of_relativeDimension_eq C f L F s hdim hX hF
          hSupp hL hs hδ,
        denominatorQuotientCycle_apply_of_relativeDimension_eq C f L F s hdim hX hF hSupp hL hs
          hδ]
      have hfull : _root_.SheafOfModules.supp F = Set.univ :=
        (_root_.SheafOfModules.supp_eq_moduleSheaf_supp F).symm.trans hSupp
      have hsets : {η : X | η ∈ genericPoints X ∧ η ⤳ x ∧
            relativeDimension C.dimensionFunction f η = k + 1} =
          {η : X | η ∈ _root_.SheafOfModules.supp F ∧ η ⤳ x ∧
            relativeDimension C.dimensionFunction f η = k + 1} :=
        Set.ext fun η => ⟨fun h => ⟨by rw [hfull]; trivial, h.2⟩,
          fun h => ⟨mem_genericPoints_of_relativeDimension_eq C f hdim h.2.2, h.2⟩⟩
      refine Eq.trans hid (finsum_mem_congr hsets fun η hη => ?_)
      have hηgp := mem_genericPoints_of_relativeDimension_eq C f hdim hη.2.2
      refine congrArg (fun z : ℤ => sheafMultiplicity F η * z) ?_
      refine Eq.trans (componentOrdAt_sub_eq_componentDivisorCycle_apply C f L s hL hs hηgp
        hη.2.2 hη.2.1 hδ (stalkIdeal_integralComponentAt_mem_minimalPrimes hηgp hη.2.1)
        hxV hbas hbt ha hb) ?_
      exact (componentDivisorCoefficient_eq C f L s hL hs hηgp hη.2.2 x).symm
    · have hQ1 : x ∉ SheafOfModules.supp (denominatorQuotientDecl L F s) := fun h =>
        hx (denominatorIdealTimesModuleι_cokernel_support X L F s h)
      have hQ2 : x ∉ SheafOfModules.supp
          (@DenominatorStalk.denominatorSectionQuotientDecl X L F s
            (LocallyOfFiniteType.isLocallyNoetherian f) hL hs inferInstance hF hSupp) := fun h =>
        hx (denominatorIdealTimesModuleMul_cokernel_supp X L F s hL hs hF hSupp h)
      rw [denominatorSectionQuotientCycle_apply_of_relativeDimension_eq C f L F s hdim hX hF
          hSupp hL hs hδ,
        denominatorQuotientCycle_apply_of_relativeDimension_eq C f L F s hdim hX hF hSupp hL hs
          hδ,
        sheafMultiplicity_eq_zero_of_notMem_supp _ hQ1,
        sheafMultiplicity_eq_zero_of_notMem_supp _ hQ2, sub_self]
      refine (finsum_mem_eq_zero_of_forall_eq_zero fun η hη => ?_).symm
      have hηgp := mem_genericPoints_of_relativeDimension_eq C f hdim hη.2.2
      refine mul_eq_zero_of_right _ (Eq.trans
        (componentDivisorCoefficient_eq C f L s hL hs hηgp hη.2.2 x) ?_)
      exact componentDivisorCycle_apply_eq_zero_of_notMem_denominatorBadLocus X L s C f hL hs
        hηgp hη.2.2 hη.2.1 hδ
        (stalkIdeal_integralComponentAt_mem_minimalPrimes hηgp hη.2.1) hx
  · rw [denominatorSectionQuotientCycle_apply_of_relativeDimension_ne C f L F s hdim hX hF hSupp
        hL hs hδ,
      denominatorQuotientCycle_apply_of_relativeDimension_ne C f L F s hdim hX hF hSupp hL hs hδ,
      sub_self]
    refine (finsum_mem_eq_zero_of_forall_eq_zero fun η hη => ?_).symm
    have hηgp := mem_genericPoints_of_relativeDimension_eq C f hdim hη.2.2
    refine mul_eq_zero_of_right _ (Eq.trans
      (componentDivisorCoefficient_eq C f L s hL hs hηgp hη.2.2 x) ?_)
    by_contra hne
    exact hδ ((mem_cyclesOfDimension_iff_forall_point C f k _).1
      (componentDivisorCycle C f L s hL hs hηgp hη.2.2).2 x hne)

end Stacks.Chow

end
