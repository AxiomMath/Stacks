module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.RingHom.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.LocalProperties.StandardCover
public import StacksFrontier.RingTheory.Noetherian.Spec
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt

/-!
# Local properties of rings, and schemes that satisfy one locally

A property of commutative rings is *local* when it is preserved by localization at an element
and can be checked on a finite standard open covering. Such a property can be imposed on a
scheme pointwise, by asking that every point have an affine open neighbourhood whose ring of
sections satisfies it.

Three properties are shown to be local: being of finite type over the integers, being
Noetherian and Cohen–Macaulay, and being Noetherian and regular.

## Main definitions

* `CommRing.PropertyIsLocal` says that a property of commutative rings is local.
* `AlgebraicGeometry.IsLocally` says that a scheme locally satisfies a given property of
  commutative rings.

## Main results

* `CommRing.isNoetherianCohenMacaulayRing_propertyIsLocal`: being Noetherian and Cohen–Macaulay
  is a local property.
* `CommRing.isRegularRing_propertyIsLocal`: being Noetherian and regular is a local property.
* `CommRing.finiteType_int_isLocal`: being of finite type over `ℤ` is a local property.

Those three are the whole mathematical content of Tag 01OT, whose remaining clause only invites
further properties to be added.

* `AlgebraicGeometry.isReduced_iff_isLocally_isReduced`: a scheme is reduced if and only if it
  locally satisfies reducedness of rings. This is Tag 01OS, not part of 01OT.

## Implementation notes

A ring property is represented as a predicate on types equipped with a commutative ring
structure. Localization preservation is stated for any ring satisfying the universal property of
localization away from an element, while the covering condition is expressed by a finite family
whose range spans the unit ideal, with the local rings represented by the canonical
`Localization.Away` construction.

Affine open neighbourhoods are represented by elements of `Scheme.affineOpens`, so their
affineness is part of their type. `IsLocally` is an abbreviation, allowing clients to use its
pointwise existential characterization directly.

Noetherianity is included in the Cohen–Macaulay property itself, since `IsCohenMacaulayRing`
takes a Noetherian instance; the existential instance packages the two conditions without
imposing Noetherianity on the ambient class of rings. Mathlib's `IsRegularRing`, by contrast,
already includes `IsNoetherianRing`, so it expresses both conditions in the regular case without
a separate conjunction.

## References

* [Stacks Project, Tag 01OP](https://stacks.math.columbia.edu/tag/01OP)
* [Stacks Project, Tag 01OQ](https://stacks.math.columbia.edu/tag/01OQ)
* [Stacks Project, Tag 01OS](https://stacks.math.columbia.edu/tag/01OS)
* [Stacks Project, Tag 01OT](https://stacks.math.columbia.edu/tag/01OT)
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace CommRing

/-- A property of commutative rings is local if it is preserved by localization away from
an element and descends from every finite family of such localizations whose elements
generate the unit ideal. -/
@[stacks 01OP] structure PropertyIsLocal (P : ∀ (R : Type u) [CommRing R], Prop) : Prop where
  /-- The property passes to any ring realizing the localization away from an element. -/
  localizationAwayPreserves : ∀ {R : Type u} [hR : CommRing R] (f : R) (S : Type u)
    [hS : CommRing S] [Algebra R S] [IsLocalization.Away f S], @P R hR → @P S hS
  /-- The property descends from a finite standard open covering of the spectrum. -/
  ofLocalizationSpan : ∀ {R : Type u} [hR : CommRing R] {ι : Type u} [Finite ι] (f : ι → R),
    Ideal.span (Set.range f) = ⊤ → (∀ i, P (Localization.Away (f i))) → @P R hR

/-- Transport a `ℤ`-algebra structure, which is unique, across the finite-type property. -/
private theorem finiteType_int_transfer_algebra {A : Type*} [CommRing A] (a b : Algebra ℤ A)
    (h : @Algebra.FiniteType ℤ A _ _ a) : @Algebra.FiniteType ℤ A _ _ b :=
  Subsingleton.elim a b ▸ h

/-- Being a finite-type algebra over the integers is a local property of
commutative rings. -/
@[stacks 01OT "part (3) (absolutely Noetherian): being of finite type over ℤ is a local property"]
theorem finiteType_int_isLocal :
    PropertyIsLocal
      (fun (R : Type u) [CommRing R] => Algebra.FiniteType ℤ R) := by
  refine ⟨?_, ?_⟩
  · intro R _ f S _ _ _ hR
    exact hR.trans (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) S)
  · intro R _ ι _ f hcov hlocal
    refine Algebra.FiniteType.of_span_eq_top_target (Set.range f) hcov ?_
    rintro _ ⟨i, rfl⟩
    exact finiteType_int_transfer_algebra (Ring.toIntAlgebra _) _ (hlocal i)

/-- A ring isomorphism of local rings does not decrease the depth of the maximal ideal. -/
private theorem localRingDepth_le_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    localRingDepth A ≤ localRingDepth B := by
  unfold localRingDepth
  refine iSup_le fun s => ?_
  let t : {s : List B // (∀ x ∈ s, x ∈ IsLocalRing.maximalIdeal B) ∧
      RingTheory.Sequence.IsRegular B s} := by
    refine ⟨s.val.map e, ?_, ?_⟩
    · intro b hb
      rcases List.mem_map.mp hb with ⟨a, ha, rfl⟩
      rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
      exact Ideal.mem_map_of_mem _ (s.property.1 a ha)
    · exact (AddEquiv.isRegular_congr (e := e.toAddEquiv)
        (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr
          fun r _ x => by simp [e.map_mul r x]))).1 s.property.2
  simpa [t] using (le_iSup_of_le t le_rfl : (t.val.length : ℕ∞) ≤ _)

/-- Isomorphic local rings have the same depth. -/
private theorem localRingDepth_eq_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    localRingDepth A = localRingDepth B :=
  le_antisymm (localRingDepth_le_of_ringEquiv e) (localRingDepth_le_of_ringEquiv e.symm)

/-- The Cohen–Macaulay condition on a Noetherian local ring is invariant under isomorphism. -/
private theorem isCohenMacaulayLocalRingPropForm_iff_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] (e : A ≃+* B) :
    IsCohenMacaulayLocalRingPropForm A ↔ IsCohenMacaulayLocalRingPropForm B := by
  simp only [IsCohenMacaulayLocalRingPropForm, localRingDepth_eq_of_ringEquiv e,
    ringKrullDim_eq_of_ringEquiv e]

/-- For a prime `p` and a family of elements spanning the unit ideal, some element `f i` is
outside `p`, and `R_p` is isomorphic to a localization of `R[1/f i]` at a prime. -/
private theorem exists_away_prime_ringEquiv {R : Type u} [CommRing R] {ι : Type u} (f : ι → R)
    (hf : Ideal.span (Set.range f) = ⊤) (p : Ideal R) [hp : p.IsPrime] :
    ∃ (i : ι) (q : Ideal (Localization.Away (f i))) (_ : q.IsPrime),
      Nonempty (Localization.AtPrime p ≃+* Localization.AtPrime q) := by
  obtain ⟨i, hfi⟩ : ∃ i, f i ∉ p := by
    by_contra! h
    exact hp.ne_top (top_le_iff.mp (hf ▸ Ideal.span_le.mpr (Set.range_subset_iff.mpr h)))
  have hdisj : Disjoint (Submonoid.powers (f i) : Set R) p :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime (f i)).mpr hfi
  have : (p.map (algebraMap R (Localization.Away (f i)))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (f i)) _ p hp hdisj
  exact ⟨i, _, this, ⟨(Localization.AtPrime.algEquivMapAway (R := R) p (f i)
    (IsLocalization.under_map_of_isPrime_disjoint _ _ hp hdisj)).toRingEquiv⟩⟩

/-- The property of a commutative ring of being Noetherian and Cohen–Macaulay is local. -/
@[stacks 01OT "part (1) (Cohen-Macaulay): being Noetherian and Cohen-Macaulay is a local property"]
public theorem isNoetherianCohenMacaulayRing_propertyIsLocal :
    PropertyIsLocal
      (fun (R : Type u) [hR : CommRing R] =>
        ∃ hN : IsNoetherianRing R, @IsCohenMacaulayRing R hR hN) := by
  refine ⟨?_, ?_⟩
  · rintro R _ f S _ _ _ ⟨hN, hCM⟩
    have : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers f) S hN
    refine ⟨inferInstance, fun q _ => ?_⟩
    let p : Ideal R := q.comap (algebraMap R S)
    have : p.IsPrime := Ideal.comap_isPrime _ _
    have : IsLocalization.AtPrime (Localization.AtPrime q) p :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        (M := Submonoid.powers f) (S := S) (T := Localization.AtPrime q) q
    exact (isCohenMacaulayLocalRingPropForm_iff_of_ringEquiv
      (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
        (Localization.AtPrime q)).toRingEquiv).mp (hCM p)
  · intro R _ ι _ f hf hlocal
    have : IsNoetherianRing R :=
      IsNoetherianRing.of_localizationSpan_range f hf fun i => (hlocal i).1
    refine ⟨inferInstance, fun p hp => ?_⟩
    obtain ⟨i, q, hq, ⟨e⟩⟩ := exists_away_prime_ringEquiv f hf p
    have : IsNoetherianRing (Localization.Away (f i)) := (hlocal i).1
    exact (isCohenMacaulayLocalRingPropForm_iff_of_ringEquiv e).mpr ((hlocal i).2 q)

/-- Being a Noetherian regular ring is local on the spectrum. -/
@[stacks 01OT "part (2) (regular): being Noetherian and regular is a local property"]
theorem isRegularRing_propertyIsLocal :
    PropertyIsLocal (fun (R : Type u) [CommRing R] => IsRegularRing R) := by
  refine ⟨?_, ?_⟩
  · intro R _ f S _ _ _ _
    exact isRegularRing_of_isLocalization (Submonoid.powers f)
  · intro R _ ι _ f hf hlocal
    have : IsNoetherianRing R :=
      IsNoetherianRing.of_localizationSpan_range f hf fun i => by
        have : IsRegularRing (Localization.Away (f i)) := hlocal i
        infer_instance
    rw [isRegularRing_iff]
    intro p hp
    obtain ⟨i, q, hq, ⟨e⟩⟩ := exists_away_prime_ringEquiv f hf p
    have : IsRegularRing (Localization.Away (f i)) := hlocal i
    exact IsRegularLocalRing.of_ringEquiv e.symm

end CommRing

namespace AlgebraicGeometry

/-- A scheme is locally `P` if every point belongs to an affine open whose ring of sections
satisfies `P`. -/
@[stacks 01OQ] abbrev IsLocally (P : (R : Type u) → [CommRing R] → Prop) (X : Scheme.{u}) :
    Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ P Γ(X, U)

/-- A scheme is reduced exactly when it is locally reduced: every point has an affine open
neighbourhood whose ring of sections is a reduced ring. -/
@[stacks 01OS "Both directions, for an arbitrary scheme and with no further hypotheses:
`AlgebraicGeometry.IsReduced X` is equivalent to `IsLocally` applied to reducedness of rings,
which is `locally reduced` in the sense of Definition 01OQ."]
theorem isReduced_iff_isLocally_isReduced (X : Scheme.{u}) :
    IsReduced X ↔ IsLocally (fun (R : Type u) [CommRing R] => _root_.IsReduced R) X := by
  constructor
  · intro _ x
    obtain ⟨U, hU, hxU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
    exact ⟨⟨U, hU⟩, hxU, inferInstance⟩
  · intro h
    have hstalk : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
      intro x
      obtain ⟨U, hxU, hred⟩ := h x
      have hredU : _root_.IsReduced Γ(X, (U : X.Opens)) := hred
      have : IsReduced (U : X.Opens).toScheme := isReduced_of_isOpenImmersion U.2.isoSpec.hom
      have : _root_.IsReduced ((U : X.Opens).toScheme.presheaf.stalk ⟨x, hxU⟩) :=
        isReduced_stalk_of_isReduced _ _
      exact isReduced_of_injective
        (Scheme.Opens.stalkIso (U : X.Opens) ⟨x, hxU⟩).inv.hom
        (Scheme.Opens.stalkIso (U : X.Opens) ⟨x, hxU⟩).symm.commRingCatIsoToRingEquiv.injective
    exact isReduced_of_isReduced_stalk X

end AlgebraicGeometry

end
