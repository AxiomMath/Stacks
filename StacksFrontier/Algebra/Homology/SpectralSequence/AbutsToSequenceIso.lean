module

public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo

/-!
# Abutment transports along an isomorphism of spectral sequences

`StacksFrontier/Algebra/Homology/SpectralSequence/AbutsToTransport.lean` moves
`CategoryTheory.SpectralSequence.AbutsTo` along an isomorphism of the *abutment*. This file moves
it along an isomorphism of the *spectral sequence*: two isomorphic spectral sequences have the
same infinity pages, so one abuts to a graded object exactly when the other does.

The consumer is a spectral sequence produced as the value of a functor -- a right derived functor,
say -- whose convergence is proved on an isomorphic sequence built by hand from a chosen
resolution. `CategoryTheory.SpectralSequence.AbutsTo.of_iso` cannot do that: it keeps the
sequence fixed and changes the abutment.

## Main results

* `CategoryTheory.SpectralSequence.hasEdgeMonoAt_of_iso`,
  `CategoryTheory.SpectralSequence.hasEdgeEpiAt_of_iso` and
  `CategoryTheory.SpectralSequence.hasPageInfinityAt_of_iso`: the vanishing of the differentials
  into and out of a bidegree, and therefore the existence of the infinity page there, transport
  along an isomorphism of spectral sequences.
* `CategoryTheory.SpectralSequence.AbutsTo.ofSequenceIso`: **abutment transports along an
  isomorphism of spectral sequences.**

## Implementation notes

The identification of the two infinity pages is
`CategoryTheory.SpectralSequence.Hom.mapPageInfinity` of the inverse isomorphism, which is
invertible by `CategoryTheory.SpectralSequence.Hom.isIso_mapPageInfinity_of_isIso_hom` -- the
map induced on a single page by an isomorphism of spectral sequences is an isomorphism. No
compatibility between the identifications at two bidegrees is needed: `AbutsTo` is a proposition
whose witnessing isomorphisms are existentially quantified.

## References

* [Stacks Project, Tag 01F2](https://stacks.math.columbia.edu/tag/01F2)
* [Stacks Project, Tag 012W](https://stacks.math.columbia.edu/tag/012W)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

/-- A morphism of spectral sequences is an isomorphism on each page, when it is an
isomorphism. -/
instance isIso_hom_of_isIso {E E' : SpectralSequence C c r₀} (f : E ⟶ E') [IsIso f] (r : ℤ)
    (hr : r₀ ≤ r) : IsIso (f.hom r hr) :=
  inferInstanceAs (IsIso ((pageFunctor C c r₀ r hr).map f))

/-- A morphism of spectral sequences is an isomorphism in each bidegree of each page, when it is
an isomorphism. -/
instance isIso_hom_f_of_isIso {E E' : SpectralSequence C c r₀} (f : E ⟶ E') [IsIso f] (r : ℤ)
    (hr : r₀ ≤ r) (pq : ι) : IsIso ((f.hom r hr).f pq) :=
  inferInstanceAs (IsIso ((HomologicalComplex.eval C (c r) pq).map (f.hom r hr)))

/-- A differential vanishes on the target of a morphism of complexes that is epi at its source
degree, when it vanishes on the source. -/
private theorem d_eq_zero_of_hom_of_epi {c' : ComplexShape ι} {K L : HomologicalComplex C c'}
    (f : K ⟶ L) {i j : ι} [Epi (f.f i)] (h : K.d i j = 0) : L.d i j = 0 := by
  have hcomm := f.comm i j
  rw [h, zero_comp] at hcomm
  exact (cancel_epi (f.f i)).1 (hcomm.trans comp_zero.symm)

/-- **The differentials into a bidegree vanish on a page of a spectral sequence exactly when they
do on the isomorphic sequence.** -/
theorem hasEdgeMonoAt_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : ι) (r : ℤ)
    [E.HasEdgeMonoAt pq r] : E'.HasEdgeMonoAt pq r where
  le := E.le₀_of_hasEdgeMonoAt pq r
  zero pq' := by
    exact d_eq_zero_of_hom_of_epi (e.hom.hom r (E.le₀_of_hasEdgeMonoAt pq r))
      (E.d_eq_zero_of_hasEdgeMonoAt pq' pq r)

/-- **The differentials out of a bidegree vanish on a page of a spectral sequence exactly when
they do on the isomorphic sequence.** -/
theorem hasEdgeEpiAt_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : ι) (r : ℤ)
    [E.HasEdgeEpiAt pq r] : E'.HasEdgeEpiAt pq r where
  le := E.le₀_of_hasEdgeEpiAt pq r
  zero pq' := by
    exact d_eq_zero_of_hom_of_epi (e.hom.hom r (E.le₀_of_hasEdgeEpiAt pq r))
      (E.d_eq_zero_of_hasEdgeEpiAt pq pq' r)

/-- **The infinity page exists at a bidegree exactly when it does on the isomorphic sequence.**
The two sequences have isomorphic pages, compatibly with the differentials, so a differential
vanishes on one exactly when it vanishes on the other. -/
theorem hasPageInfinityAt_of_iso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : ι)
    [E.HasPageInfinityAt pq] : E'.HasPageInfinityAt pq where
  nonempty_hasEdgeMonoSet := by
    obtain ⟨r, hr⟩ := E.nonempty_hasEdgeMonoSet pq
    exact ⟨r, hr.1, fun r' hrr' => have := hr.2 r' hrr'; hasEdgeMonoAt_of_iso e pq r'⟩
  nonempty_hasEdgeEpiSet := by
    obtain ⟨r, hr⟩ := E.nonempty_hasEdgeEpiSet pq
    exact ⟨r, hr.1, fun r' hrr' => have := hr.2 r' hrr'; hasEdgeEpiAt_of_iso e pq r'⟩

/-- **The infinity pages of two isomorphic spectral sequences are isomorphic.** -/
noncomputable def pageInfinityIsoOfIso {E E' : SpectralSequence C c r₀} (e : E ≅ E') (pq : ι)
    [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq] :
    E'.pageInfinity pq ≅ E.pageInfinity pq :=
  haveI : IsIso (Hom.mapPageInfinity e.inv pq) :=
    Hom.isIso_mapPageInfinity_of_isIso_hom e.inv r₀ pq (hr := le_rfl) inferInstance
  asIso (Hom.mapPageInfinity e.inv pq)

/-- **Abutment transports along an isomorphism of spectral sequences.** If `E` abuts to the
graded object `H` and `E ≅ E'`, then `E'` abuts to `H`: the witnessing filtration of `H` is
unchanged, and its graded pieces are identified with the infinity page of `E'` through
`pageInfinityIsoOfIso`. -/
theorem AbutsTo.ofSequenceIso {E E' : CohomologicalSpectralSequence C r₀} {H : ℤ → C}
    (hE : AbutsTo E H) (e : E ≅ E') : AbutsTo E' H := by
  obtain ⟨hinf, F, hF, hbounds, hgr⟩ := hE
  have hinf' : ∀ p q : ℤ, E'.HasPageInfinityAt (p, q) := fun p q =>
    have := hinf p q; hasPageInfinityAt_of_iso e (p, q)
  refine ⟨hinf', F, hF, hbounds, fun p q => ?_⟩
  have := hinf p q
  have := hinf' p q
  exact ⟨pageInfinityIsoOfIso e (p, q) ≪≫ (hgr p q).some⟩

end CategoryTheory.SpectralSequence

end
