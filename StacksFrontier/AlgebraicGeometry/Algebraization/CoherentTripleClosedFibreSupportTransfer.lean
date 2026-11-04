module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedFibreVanishing

/-!
# The closed-fibre support of a triple across the gluing, without assuming the punctured member
zero

For a coherent triple `T`, the gluing isomorphism `T.alpha` and
`AlgebraicGeometry.supp_pullback_eq_preimage` give the equality of sets

`ι ⁻¹' Supp T.F₀ = Supp (i^* T.F)`,

for `ι` the open immersion of the punctured closed fibre into the closed fibre and `i` the
closed immersion of the punctured closed fibre into the punctured spectrum. Consequently the
statements of `StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleClosedFibreVanishing`
hold at the hypothesis `Supp (i^* T.F) = ∅` in place of `IsZero T.F`.

## Main results

* `Stacks.Algebraization.CoherentTriple.preimage_supp_F₀_eq_supp_pullback_F`: **the part of the
  support of the closed-fibre member lying over the punctured closed fibre is the support of the
  inverse image of the punctured-spectrum member there**, with no hypothesis on the triple.
* `Stacks.Algebraization.CoherentTriple.notMem_supp_F₀_of_mem_puncturedClosedFibre_of_isEmpty`,
  `Stacks.Algebraization.CoherentTriple.supp_F₀_subset_closedPoint_of_isEmpty` and
  `Stacks.Algebraization.CoherentTriple.isZero_F₀_of_isEmpty`: the three steps of
  `CoherentTripleClosedFibreVanishing` restated at the weaker hypothesis. The last is the
  vanishing of the closed-fibre member, given that the closed point is not an associated point
  of it.

## References

* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace Stacks.Algebraization

/-! ### The support of the closed-fibre member over the punctured closed fibre -/

/-- **The part of the support of the closed-fibre member lying over the punctured closed fibre is
the support of the inverse image of the punctured-spectrum member there.** -/
public theorem CoherentTriple.preimage_supp_F₀_eq_supp_pullback_F {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} (T : CoherentTriple A f) :
    (puncturedClosedFibre A f).ι ⁻¹' SheafOfModules.supp T.F₀ =
      SheafOfModules.supp ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))).obj T.F) := by
  rw [← AlgebraicGeometry.supp_pullback_eq_preimage (puncturedClosedFibre A f).ι T.F₀]
  exact (SheafOfModules.supp_eq_of_iso T.alpha).symm

/-! ### The three steps at the weaker hypothesis -/

/-- **No point of the punctured closed fibre lies in the support of the closed-fibre member**, as
soon as the inverse image of the punctured-spectrum member on the punctured closed fibre has
empty support. -/
public theorem CoherentTriple.notMem_supp_F₀_of_mem_puncturedClosedFibre_of_isEmpty {A : Type u}
    [CommRing A] [IsLocalRing A] {f : A} (T : CoherentTriple A f)
    (hT : SheafOfModules.supp ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A))).obj T.F) = ∅)
    {y : closedFibre A f} (hy : y ∈ (puncturedClosedFibre A f : Set (closedFibre A f))) :
    y ∉ SheafOfModules.supp T.F₀ := by
  intro hmem
  have h : (puncturedClosedFibre A f).ι ⟨y, hy⟩ ∈ SheafOfModules.supp T.F₀ := by simpa using hmem
  exact Set.eq_empty_iff_forall_notMem.mp hT _ (T.preimage_supp_F₀_eq_supp_pullback_F.subset h)

/-- **The support of the closed-fibre member is contained in the closed point of the closed
fibre**, as soon as the inverse image of the punctured-spectrum member on the punctured closed
fibre has empty support and `f` lies in the maximal ideal. -/
public theorem CoherentTriple.supp_F₀_subset_closedPoint_of_isEmpty {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A)
    (T : CoherentTriple A f)
    (hT : SheafOfModules.supp ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A))).obj T.F) = ∅) :
    SheafOfModules.supp T.F₀ ⊆
      {(IsLocalRing.closedPoint (A ⧸ Ideal.span {f}) : closedFibre A f)} := by
  intro y hy
  by_contra hne
  refine T.notMem_supp_F₀_of_mem_puncturedClosedFibre_of_isEmpty hT ?_ hy
  rw [puncturedClosedFibre_eq_puncturedSpectrum A f hf]
  exact hne

/-- **The closed-fibre member of a coherent triple vanishes** as soon as the inverse image of its
punctured-spectrum member on the punctured closed fibre has empty support and the closed point of
the closed fibre is not an associated point of the closed-fibre member. -/
public theorem CoherentTriple.isZero_F₀_of_isEmpty {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {f : A} [IsLocalRing (A ⧸ Ideal.span {f})] (hf : f ∈ maximalIdeal A)
    (T : CoherentTriple A f)
    (hT : SheafOfModules.supp ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
      (Stacks.Divisors.puncturedSpectrum A))).obj T.F) = ∅)
    (hass : ¬ Stacks.Divisors.IsAssociatedPoint T.F₀
      (IsLocalRing.closedPoint (A ⧸ Ideal.span {f}))) :
    IsZero T.F₀ := by
  have : T.F₀.IsCoherent := T.coherent_F₀
  have : T.F₀.IsQuasicoherent := isQuasicoherent_of_isCoherent _
  rw [AlgebraicGeometry.isZero_iff_associatedPoints_eq_empty]
  refine Set.eq_empty_iff_forall_notMem.2 fun y hy => hass ?_
  have hsupp : y = (IsLocalRing.closedPoint (A ⧸ Ideal.span {f}) : closedFibre A f) :=
    CoherentTriple.supp_F₀_subset_closedPoint_of_isEmpty hf T hT
      (AlgebraicGeometry.associatedPoints_subset_support T.F₀ hy)
  exact hsupp ▸ hy

end Stacks.Algebraization

end
