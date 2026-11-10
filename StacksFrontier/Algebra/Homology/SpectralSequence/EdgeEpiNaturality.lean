module

public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity

/-!
# Naturality of the edge epimorphisms of a spectral sequence

`StacksCore/Algebra/Homology/SpectralSequence/PageInfinity.lean` builds, for a position `pq` from
which all differentials vanish on the page `r` on, the edge epimorphism
`E.edgeEpi pq r : E_r^{pq} ⟶ E_∞^{pq}`, as the composite `E.edgeEpiSteps` of the one-step maps
`E.edgeEpiStep` of `StacksCore/Algebra/Homology/SpectralSequence/EdgeStep.lean` followed by the
identification of a late page with the infinity page. It proves the naturality of the *monomorphism*
side -- `edgeMonoStep_naturality`, `edgeMonoSteps_naturality` -- and leaves the epimorphism side as
a `TODO`. This file supplies it: a morphism of spectral sequences commutes with `edgeEpiStep`, with
`edgeEpiSteps` and hence with `edgeEpi` and `SpectralSequence.Hom.mapPageInfinity`.

That last square is what makes the bottom-row comparison map
`E_2^{n,0} ⟶ E_∞^{n,0} ⟶ \mathrm{gr}^n H^n ⟶ H^n` of a functorial first-quadrant abutment a
morphism of *functors* rather than a family of maps: at `(n, 0)` with `n ≥ 2` the differentials
*into* the position do not vanish on the second page, so `E_2^{n,0}` is not the infinity page
there and `pageInfinityIso` -- which is what the degree-zero corner argument of
`StacksFrontier/CategoryTheory/Sites/Hypercovering/CohomologyAsColimit.lean` uses -- is unavailable.

## Main results

* `CategoryTheory.SpectralSequence.Hom.edgeEpiStep_naturality`: a morphism of spectral sequences
  commutes with the one-step edge epimorphism `E_r^{pq} ⟶ E_{r+1}^{pq}`.
* `CategoryTheory.SpectralSequence.Hom.edgeEpiSteps_naturality`: the same for the composite
  `E_r^{pq} ⟶ E_{r'}^{pq}`.
* `CategoryTheory.SpectralSequence.Hom.edgeEpi_naturality`: the same for the edge epimorphism
  `E_r^{pq} ⟶ E_∞^{pq}` and `SpectralSequence.Hom.mapPageInfinity`.

## Implementation notes

`edgeEpiStep_naturality` is the dual of upstream's `edgeMonoStep_naturality`, but it is not
obtained from it by duality: it is proved directly, by composing with the inverse of the
homology identification `E.iso r r'` so that `edgeEpiStep` becomes the projection to opcycles
(`edgeEpiStep_comp_iso_inv`), after which the square is the naturality of `homologyι` and of
`pOpcycles`.

`edgeEpi_naturality` is stated at an arbitrary page `r` from which the differentials out of `pq`
vanish, with *no* hypothesis that the differentials into `pq` vanish there -- that is the whole
point, since the edge epimorphism exists precisely in that asymmetric situation.  Its proof
passes to the page `max r (max (E.rMin pq) (E'.rMin pq))`, where both edge classes hold for both
spectral sequences, so that `SpectralSequence.Hom.mapPageInfinity_eq` applies.

## References

* [Stacks Project, Tag 011N](https://stacks.math.columbia.edu/tag/011N)
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C : Type*} [Category* C] [Abelian C]
  {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence.Hom

variable {E E' : SpectralSequence C c r₀} (f : E ⟶ E')

/-- **Naturality of `edgeEpiStep`**: a morphism of spectral sequences commutes with the one-step
edge epimorphism `E_r^{pq} ⟶ E_{r'}^{pq}` (`r' = r + 1`) attached to the vanishing of the
differentials out of `pq` on the page `r`.

This is the dual of `CategoryTheory.SpectralSequence.Hom.edgeMonoStep_naturality`, which the
port of mathlib#25848 leaves as its only `TODO`. -/
@[reassoc]
lemma edgeEpiStep_naturality (pq : ι) (r r' : ℤ) [E.HasEdgeEpiAt pq r] [E'.HasEdgeEpiAt pq r]
    (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    E.edgeEpiStep pq r r' hrr' ≫ (f.hom r').f pq =
      (f.hom r).f pq ≫ E'.edgeEpiStep pq r r' hrr' := by
  have h₁ : (f.hom r').f pq ≫ (E'.iso r r' pq hrr' hr).inv =
      (E.iso r r' pq hrr' hr).inv ≫ HomologicalComplex.homologyMap (f.hom r hr) pq := by
    rw [Iso.eq_inv_comp, ← assoc, Iso.comp_inv_eq, f.comm r r' pq hrr' hr]
  rw [← cancel_mono (E'.iso r r' pq hrr' hr).inv, assoc, assoc,
    E'.edgeEpiStep_comp_iso_inv pq r r', h₁, E.edgeEpiStep_comp_iso_inv_assoc pq r r',
    ← cancel_mono ((E'.page r hr).isoHomologyι pq _ rfl (by simp)).hom]
  simp [HomologicalComplex.homologyι_naturality, HomologicalComplex.p_opcyclesMap]

/-- **Naturality of `edgeEpiSteps`**: a morphism of spectral sequences commutes with the
composite edge epimorphism `E_r^{pq} ⟶ E_{r'}^{pq}`, for `r ≤ r'` and all the differentials out
of `pq` vanishing from the page `r` on. -/
@[reassoc]
lemma edgeEpiSteps_naturality (pq : ι) (r r' : ℤ)
    (hrr' : r ≤ r' := by lia) (hr₀ : r₀ ≤ r := by lia)
    [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq]
    [E.HasEdgeEpiAtFrom pq r] [E'.HasEdgeEpiAtFrom pq r] :
    E.edgeEpiSteps pq r r' hrr' ≫ (f.hom r').f pq =
      (f.hom r).f pq ≫ E'.edgeEpiSteps pq r r' hrr' := by
  obtain ⟨k, hk⟩ := Int.le.dest hrr'
  revert r'
  induction k with
  | zero =>
    intro r' hrr' hk
    obtain rfl : r = r' := by omega
    simp
  | succ k hk =>
    intro r' hrr' hk'
    rw [E.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r + k) r' (by lia) (by lia),
      assoc, edgeEpiStep_naturality _ _ _ _ (by lia) (by lia),
      ← assoc, hk (r + k) (by lia) rfl, assoc,
      E'.edgeEpiSteps_eq_edgeEpiSteps_comp_edgeEpiStep pq r (r + k) r' (by lia) (by lia)]

/-- **Naturality of the edge epimorphism `E_r^{pq} ⟶ E_∞^{pq}`**: it commutes with the map
`SpectralSequence.Hom.mapPageInfinity` a morphism of spectral sequences induces on the infinity
pages.

No hypothesis is made at `pq` on the differentials *into* `pq`, which is what distinguishes this
from `CategoryTheory.SpectralSequence.Hom.mapPageInfinity_eq`: the proof passes to a page late
enough for both edge classes to hold for both spectral sequences, and
`edgeEpiSteps_naturality` transports the square back to the page `r`. -/
lemma edgeEpi_naturality (pq : ι) (r : ℤ) (hr₀ : r₀ ≤ r := by lia)
    [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq]
    [E.HasEdgeEpiAtFrom pq r] [E'.HasEdgeEpiAtFrom pq r] :
    (f.hom r hr₀).f pq ≫ E'.edgeEpi pq r = E.edgeEpi pq r ≫ mapPageInfinity f pq := by
  have hrs : r ≤ max r (max (E.rMin pq) (E'.rMin pq)) := le_max_left _ _
  set s := max r (max (E.rMin pq) (E'.rMin pq)) with hs
  have hs₀ : r₀ ≤ s := hr₀.trans hrs
  have : E.HasEdgeMonoAtFrom pq s :=
    E.hasEdgeMonoAtFrom_of_GE pq (E.rMin pq) s ((le_max_left _ _).trans (le_max_right r _))
  have : E.HasEdgeEpiAtFrom pq s := E.hasEdgeEpiAtFrom_of_GE pq r s hrs
  have : E'.HasEdgeMonoAtFrom pq s :=
    E'.hasEdgeMonoAtFrom_of_GE pq (E'.rMin pq) s ((le_max_right _ _).trans (le_max_right r _))
  have : E'.HasEdgeEpiAtFrom pq s := E'.hasEdgeEpiAtFrom_of_GE pq r s hrs
  rw [mapPageInfinity_eq f pq s hs₀,
    ← E.edgeEpiSteps_pageInfinityIso_inv' pq r s hrs,
    ← E'.edgeEpiSteps_pageInfinityIso_inv' pq r s hrs,
    assoc, Iso.inv_hom_id_assoc, ← edgeEpiSteps_naturality_assoc f pq r s hrs hr₀]

end SpectralSequence.Hom

end CategoryTheory

end
