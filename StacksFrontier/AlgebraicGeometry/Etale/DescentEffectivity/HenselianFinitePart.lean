module

public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.HenselianSplitting
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperComplementExtension

/-!
# Uniqueness of the finite part of a scheme over a henselian pair

Let `A` be a ring and `I ⊆ A` an ideal contained in the Jacobson radical — the first half of
being a henselian pair. A scheme finite over `Spec A` whose fibre over `Spec (A ⧸ I)` is empty
is then empty: its image is a closed subset of `Spec A`, a nonempty closed subset of an affine
scheme contains a closed point, and the prime of a closed point contains every ideal inside the
Jacobson radical, so the image would meet `V(I)`.

That makes the splitting of [Stacks, Tag 0BTN](https://stacks.math.columbia.edu/tag/0BTN)
unique: in a scheme `U` over `Spec A` there is at most one subset which is the range of a
morphism finite over `Spec A` and whose complement carries no point over `V(I)`. Uniqueness is
what [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) uses to see that the gluing
isomorphism of a descent datum preserves the splitting, the two splittings compared there being
the two pullbacks of the splitting to `X ×_S X`.

## Main results

* `Stacks.Etale.exists_mem_zeroLocus_of_isClosed`: a nonempty closed subset of `Spec A` meets
  `V(I)` when `I` lies in the Jacobson radical.
* `Stacks.Etale.mem_range_quotient_of_mem_zeroLocus`: the points of `V(I)` are the image of
  `Spec (A ⧸ I)`.
* `Stacks.Etale.isEmpty_of_isFinite_of_isEmpty_closedFibre`: **a scheme finite over `Spec A`
  with empty closed fibre is empty.**
* `Stacks.Etale.range_subset_range_of_isFinite`: **the range of a morphism finite over
  `Spec A` lies inside any subset whose complement carries no point over `V(I)`**, and
* `Stacks.Etale.range_eq_range_of_isFinite` and
  `Stacks.Etale.range_eq_range_of_isIso_coprodDesc`: **uniqueness of the finite part**, the
  second in the shape in which Tag 0BTN produces the splitting.

## Implementation notes

The statements are about ranges of morphisms into `U` rather than about open subschemes of `U`,
which keeps the argument purely topological: the only closedness used is that a finite morphism
is a closed map, applied to the preimage in the finite piece of the complement of the other
finite piece. In particular neither piece has to be shown clopen, and no subscheme structure on
the difference of the two pieces has to be built.

Emptiness of the fibre is read as emptiness of the fibre product with `Spec (A ⧸ I)`, which is
the form `Stacks.Etale.exists_coprod_isOpenImmersion_isFinite_etale_and_isEmpty_closedFiber`
produces it in; a point of the fibre product is manufactured from a point of the source and a
point of `Spec (A ⧸ I)` with the same image by
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`.

## References

* [Stacks Project, Tag 0BTN](https://stacks.math.columbia.edu/tag/0BTN)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace Stacks.Etale

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

/-- **A nonempty closed subset of `Spec A` meets `V(I)`** when `I` is contained in the Jacobson
radical of `A`: the closed subset is a zero locus of a proper ideal, which is contained in a
maximal ideal, and every maximal ideal contains the Jacobson radical. -/
theorem exists_mem_zeroLocus_of_isClosed {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I ≤ Ring.jacobson A) {C : Set (PrimeSpectrum A)} (hC : IsClosed C)
    (hne : C.Nonempty) : ∃ x ∈ C, x ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
  obtain ⟨K, hK⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal C).mp hC
  have hKne : K ≠ ⊤ := by
    rintro rfl
    obtain ⟨x, hx⟩ := hne
    rw [hK] at hx
    exact x.2.ne_top (by simpa [PrimeSpectrum.zeroLocus] using hx)
  obtain ⟨m, hm, hKm⟩ := Ideal.ne_top_iff_exists_maximal.mp hKne
  have hmax : m.IsMaximal := hm
  refine ⟨⟨m, hmax.isPrime⟩, ?_, ?_⟩
  · rw [hK]
    exact (PrimeSpectrum.mem_zeroLocus ⟨m, hmax.isPrime⟩ (K : Set A)).2 hKm
  · exact (PrimeSpectrum.mem_zeroLocus ⟨m, hmax.isPrime⟩ (I : Set A)).2
      (hI.trans (Ring.jacobson_le_of_isMaximal m))

/-- **The points of `V(I)` are exactly the image of `Spec (A ⧸ I)`.** -/
theorem mem_range_quotient_of_mem_zeroLocus {A : Type u} [CommRing A] (I : Ideal A)
    {x : PrimeSpectrum A} (hx : x ∈ PrimeSpectrum.zeroLocus (I : Set A)) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hrange : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.Quotient.mk I) : Set A) :=
    _root_.range_comap_of_surjective _ _ hsurj
  have hker : (RingHom.ker (Ideal.Quotient.mk I) : Set A) = (I : Set A) := by
    rw [Ideal.mk_ker]
  rw [hker] at hrange
  obtain ⟨y, hy⟩ : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
    rw [hrange]; exact hx
  exact ⟨y, hy⟩

/-- **A scheme finite over `Spec A` whose fibre over `Spec (A ⧸ I)` is empty is empty**, when
`I` lies in the Jacobson radical of `A`. -/
theorem isEmpty_of_isFinite_of_isEmpty_closedFibre {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I ≤ Ring.jacobson A) {W : Scheme.{u}} (p : W ⟶ Spec (CommRingCat.of A)) [IsFinite p]
    (hfib : IsEmpty (Limits.pullback p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    IsEmpty W := by
  refine ⟨fun w ↦ ?_⟩
  have hclosed : IsClosed (Set.range p.base) := by
    simpa using p.isClosedMap Set.univ isClosed_univ
  obtain ⟨x, ⟨w', hw'⟩, hxI⟩ :=
    exists_mem_zeroLocus_of_isClosed hI hclosed ⟨p.base w, w, rfl⟩
  obtain ⟨y, hy⟩ := mem_range_quotient_of_mem_zeroLocus I hxI
  obtain ⟨t, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w' y (hw'.trans hy.symm)
  exact hfib.elim t

/-- **The range of a morphism finite over `Spec A` lies inside any subset of `U` whose
complement carries no point over `V(I)`.** The preimage in the finite piece of the complement of
that subset is closed, so its image in `Spec A` is closed; were it nonempty it would meet
`V(I)`, giving a point of the excluded fibre. -/
theorem range_subset_range_of_isFinite {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I ≤ Ring.jacobson A) {U : Scheme.{u}} (q : U ⟶ Spec (CommRingCat.of A))
    {Wf Wf' Wa' : Scheme.{u}} (jf : Wf ⟶ U) (jf' : Wf' ⟶ U) (ja' : Wa' ⟶ U)
    [IsFinite (jf ≫ q)] [IsOpenImmersion jf']
    (hcov' : Set.range jf'.base ∪ Set.range ja'.base = Set.univ)
    (hfib' : IsEmpty (Limits.pullback (ja' ≫ q)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    Set.range jf.base ⊆ Set.range jf'.base := by
  by_contra hsub
  obtain ⟨u, ⟨w, rfl⟩, hu'⟩ := Set.not_subset.mp hsub
  set T : Set Wf := jf.base ⁻¹' (Set.range jf'.base)ᶜ with hT
  have hTclosed : IsClosed T :=
    (jf'.isOpenEmbedding.isOpen_range.isClosed_compl).preimage jf.continuous
  have hwT : w ∈ T := hu'
  have hC : IsClosed ((jf ≫ q).base '' T) := (jf ≫ q).isClosedMap T hTclosed
  obtain ⟨x, ⟨w', hw'T, hw'⟩, hxI⟩ :=
    exists_mem_zeroLocus_of_isClosed hI hC ⟨(jf ≫ q).base w, w, hwT, rfl⟩
  have hmem : jf.base w' ∈ Set.range ja'.base := by
    have : jf.base w' ∈ (Set.univ : Set U) := Set.mem_univ _
    rw [← hcov'] at this
    exact this.resolve_left hw'T
  obtain ⟨v, hv⟩ := hmem
  obtain ⟨y, hy⟩ := mem_range_quotient_of_mem_zeroLocus I hxI
  have hcomp : (ja' ≫ q).base v = x := by
    rw [Scheme.Hom.comp_base]
    change q.base (ja'.base v) = x
    rw [hv]
    rw [← hw']
    rfl
  obtain ⟨t, -, -⟩ := Scheme.Pullback.exists_preimage_pullback v y (hcomp.trans hy.symm)
  exact hfib'.elim t

/-- **Uniqueness of the finite part of a splitting over a henselian pair.** Two morphisms into
`U` which are finite over `Spec A` and whose complements in `U` are covered by pieces carrying
no point over `V(I)` have the same range. -/
theorem range_eq_range_of_isFinite {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I ≤ Ring.jacobson A) {U : Scheme.{u}} (q : U ⟶ Spec (CommRingCat.of A))
    {Wf Wa Wf' Wa' : Scheme.{u}} (jf : Wf ⟶ U) (ja : Wa ⟶ U) (jf' : Wf' ⟶ U) (ja' : Wa' ⟶ U)
    [IsFinite (jf ≫ q)] [IsFinite (jf' ≫ q)] [IsOpenImmersion jf] [IsOpenImmersion jf']
    (hcov : Set.range jf.base ∪ Set.range ja.base = Set.univ)
    (hcov' : Set.range jf'.base ∪ Set.range ja'.base = Set.univ)
    (hfib : IsEmpty (Limits.pullback (ja ≫ q)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u}))
    (hfib' : IsEmpty (Limits.pullback (ja' ≫ q)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    Set.range jf.base = Set.range jf'.base :=
  Set.Subset.antisymm
    (range_subset_range_of_isFinite hI q jf jf' ja' hcov' hfib')
    (range_subset_range_of_isFinite hI q jf' jf ja hcov hfib)

/-- **The two legs of an isomorphism out of a binary coproduct cover the target.** -/
theorem union_range_eq_univ_of_isIso_coprodDesc {U Wf Wa : Scheme.{u}}
    (jf : Wf ⟶ U) (ja : Wa ⟶ U) [IsIso (coprod.desc jf ja)] :
    Set.range jf.base ∪ Set.range ja.base = Set.univ := by
  refine Set.eq_univ_of_forall fun u ↦ ?_
  obtain ⟨p, hp⟩ := (coprod.desc jf ja).surjective u
  rcases Set.eq_univ_iff_forall.mp (union_range_coprod_inl_inr Wf Wa) p with ⟨w, hw⟩ | ⟨w, hw⟩
  · refine Or.inl ⟨w, ?_⟩
    have hc : ((coprod.inl : Wf ⟶ Wf ⨿ Wa) ≫ coprod.desc jf ja).base w = u := by
      rw [Scheme.Hom.comp_base]
      change (coprod.desc jf ja).base ((coprod.inl : Wf ⟶ Wf ⨿ Wa).base w) = u
      rw [hw]; exact hp
    rwa [coprod.inl_desc] at hc
  · refine Or.inr ⟨w, ?_⟩
    have hc : ((coprod.inr : Wa ⟶ Wf ⨿ Wa) ≫ coprod.desc jf ja).base w = u := by
      rw [Scheme.Hom.comp_base]
      change (coprod.desc jf ja).base ((coprod.inr : Wa ⟶ Wf ⨿ Wa).base w) = u
      rw [hw]; exact hp
    rwa [coprod.inr_desc] at hc

/-- **Uniqueness of the finite part of a splitting over a henselian pair, in the shape produced
by Tag 0BTN**: the splitting is recorded as an isomorphism out of a binary coproduct, and the
two covering conditions are read off those isomorphisms. -/
theorem range_eq_range_of_isIso_coprodDesc {A : Type u} [CommRing A] {I : Ideal A}
    (hI : I ≤ Ring.jacobson A) {U : Scheme.{u}} (q : U ⟶ Spec (CommRingCat.of A))
    {Wf Wa Wf' Wa' : Scheme.{u}} (jf : Wf ⟶ U) (ja : Wa ⟶ U) (jf' : Wf' ⟶ U) (ja' : Wa' ⟶ U)
    [IsFinite (jf ≫ q)] [IsFinite (jf' ≫ q)] [IsOpenImmersion jf] [IsOpenImmersion jf']
    [IsIso (coprod.desc jf ja)] [IsIso (coprod.desc jf' ja')]
    (hfib : IsEmpty (Limits.pullback (ja ≫ q)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u}))
    (hfib' : IsEmpty (Limits.pullback (ja' ≫ q)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    Set.range jf.base = Set.range jf'.base :=
  range_eq_range_of_isFinite hI q jf ja jf' ja'
    (union_range_eq_univ_of_isIso_coprodDesc jf ja)
    (union_range_eq_univ_of_isIso_coprodDesc jf' ja') hfib hfib'

end Stacks.Etale

end
