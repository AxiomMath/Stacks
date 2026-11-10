module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.Proper
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

/-!
# Splitting off the proper part of the closed fibre over a henselian pair

Let `(A, I)` be a henselian pair, let `X` be separated and of finite type over `Spec A` and let
`Y` be an open and closed subscheme of the closed fibre `X₀ = X ×_{Spec A} Spec (A ⧸ I)` which is
proper over `Spec (A ⧸ I)`.  [Stacks, Tag 0CT9] asserts that `Y` is then the closed fibre of an
open and closed subscheme `W ⊆ X` which is proper over `Spec A`.

The argument has two halves.  The first is **unconditional** and is the substance of this file:
for a *proper* `f : X ⟶ Spec A`, every open and closed subset of the closed fibre is the
restriction of an open and closed subset of `X`.  Stein factorization writes `f` as
`X ⟶ f.normalization ⟶ Spec A` with the second factor integral, so that `f.normalization` is the
spectrum of an `A`-algebra `B` integral over `A`; the clopen subset is pushed forward to
`Spec (B ⧸ IB)`, lifted to an idempotent of `B` by the characterization of henselian pairs
through idempotents of integral algebras ([Stacks, Tag 09XI]), and pulled back.  The second half
compactifies `f` and cuts the resulting clopen subset of the compactification back down to `X`,
which is possible because a nonempty closed subset of `Spec A` meets the closed fibre
`V(I)`.

## Main results

* `AlgebraicGeometry.exists_isClopen_preimage_eq_of_isIntegralHom_of_henselianPair`: for an
  integral morphism to `Spec A`, every open and closed subset of the closed fibre is the
  restriction of one on the source.
* `AlgebraicGeometry.exists_isClopen_preimage_eq_of_isProper_of_henselianPair`: the same for a
  proper morphism whose Stein first factor has geometrically connected fibres.
* `AlgebraicGeometry.exists_isClopen_isProper_of_henselianPair_of_compactification`: the
  conclusion of [Stacks, Tag 0CT9], from a compactification of `f` and clause (1) of
  [Stacks, Tag 03H2].

## Implementation notes

Finite type is expressed by `AlgebraicGeometry.LocallyOfFiniteType` together with
`AlgebraicGeometry.QuasiCompact`, subschemes are represented by their immersion morphisms, and
the equality `W ×_{Spec A} Spec (A ⧸ I) = Y` is expressed by an isomorphism whose composite with
the canonical base-change immersion is the given immersion of `Y` into the closed fibre.

The main theorem carries the tag, with a part string naming the two hypotheses it carries.
Neither is the tag's own conclusion:  each is the conclusion of a *different* tag that the source
quotes as an input and that no declaration in either Lean tree supplies.

* `hcpt` is the conclusion of **[Stacks, Tag 0F41]**, Nagata's compactification theorem: a
  separated morphism of finite type to a quasi-compact quasi-separated scheme factors as a
  quasi-compact open immersion followed by a proper morphism.  Nothing in the repository proves
  it; `AlgebraicGeometry.CategoryOfCompactifications` in
  `StacksFrontier/AlgebraicGeometry/Flatness/Flattening/Compactifications.lean` takes exactly this
  existence statement as a *field* of its standing data, and the Chow's lemma of
  `StacksFrontier/AlgebraicGeometry/ChowFiniteType/Basic.lean` — the route the source takes instead
  of Nagata — is itself conditional on
  `AlgebraicGeometry.Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`.
* `hconn` is the connectedness assertion of clause (1) of **[Stacks, Tag 03H2]**, Zariski's
  connectedness theorem for the Stein factorization.  In this repository it is available only
  conditionally on [Stacks, Tag 0G7X], as
  `Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_etaleNeighborhood`, or
  unconditionally only over the points at which the local ring of `f.normalization` is its own
  residue field (`Stacks.SteinFactorization`
  `.geometricallyConnected_fiberToSpecResidueField_toNormalization_of_flat`).

With both inputs the main theorem is the tag with its two hypotheses deleted and nothing else
changed.

## References

* [Stacks Project, Tag 0CT9](https://stacks.math.columbia.edu/tag/0CT9)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
* [EGA III, Proposition 5.5.1]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Topological preliminaries -/

/-- An open and closed subset of a scheme is the range of a morphism which is both an open and a
closed immersion, namely the inclusion of the corresponding open subscheme. -/
theorem exists_isOpenImmersion_isClosedImmersion_range_eq {X : Scheme.{u}} {U : Set X}
    (hU : IsClopen U) :
    ∃ (W : Scheme.{u}) (w : W ⟶ X), IsOpenImmersion w ∧ IsClosedImmersion w ∧
      Set.range w = U := by
  let V : X.Opens := ⟨U, hU.isOpen⟩
  refine ⟨V.toScheme, V.ι, inferInstance, IsClosedImmersion.of_isPreimmersion _ ?_, ?_⟩
  · simpa [V] using hU.isClosed
  · simp [V]

/-- For a closed surjection with preconnected fibres, the image of an open and closed set is open
and closed, and the set is recovered as the preimage of its image. -/
private theorem isClopen_image_and_preimage_image_eq {X S : Type*} [TopologicalSpace X]
    [TopologicalSpace S] (f : X → S) (hclosed : IsClosedMap f) (hsurj : Function.Surjective f)
    (hconn : ∀ s, IsPreconnected (f ⁻¹' ({s} : Set S))) {U : Set X} (hU : IsClopen U) :
    IsClopen (f '' U) ∧ f ⁻¹' (f '' U) = U := by
  have hdisj : Disjoint (f '' U) (f '' Uᶜ) := by
    rw [Set.disjoint_left]
    rintro s ⟨x, hxU, hxs⟩ ⟨y, hyU, hys⟩
    exact hyU ((hconn (f y)).subset_isClopen hU
      ⟨x, by simp [hxs.trans hys.symm], hxU⟩ (by simp))
  have hcover : f '' U ∪ f '' Uᶜ = Set.univ := by
    rw [← Set.image_union, Set.union_compl_self, Set.image_univ, hsurj.range_eq]
  have hcompl : (f '' U)ᶜ = f '' Uᶜ := by
    apply Set.eq_of_subset_of_subset
    · intro s hs
      rcases show s ∈ f '' U ∪ f '' Uᶜ by rw [hcover]; trivial with hsU | hsUc
      · exact (hs hsU).elim
      · exact hsUc
    · intro s hs hsU
      exact hdisj.le_bot ⟨hsU, hs⟩
  have hpre : f ⁻¹' (f '' U) = U := by
    apply Set.eq_of_subset_of_subset
    · intro x hx
      obtain ⟨z, hzU, hxy⟩ := hx
      exact (hconn (f z)).subset_isClopen hU ⟨z, by simp, hzU⟩ (by simp [hxy])
    · intro x hx
      exact ⟨x, hx, rfl⟩
  refine ⟨⟨hclosed U hU.isClosed, ?_⟩, hpre⟩
  have hclosecompl : IsClosed (f '' U)ᶜ := by
    rw [hcompl]
    exact hclosed Uᶜ hU.compl.isClosed
  simpa using hclosecompl.isOpen_compl

/-- An open and closed subset transported along two maps with the same range: if `j` is an
embedding, `k` is continuous and the two have the same range, then an open and closed set of the
target restricting to a prescribed one along `k` also restricts to the transported one along
`j`. -/
private theorem exists_isClopen_preimage_eq_of_range_eq {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (j : X → Z) (k : Y → Z)
    (hj : Topology.IsEmbedding j) (hk : Continuous k) (hr : Set.range j = Set.range k)
    (hlift : ∀ U : Set Y, IsClopen U → ∃ V : Set Z, IsClopen V ∧ k ⁻¹' V = U)
    {U : Set X} (hU : IsClopen U) :
    ∃ V : Set Z, IsClopen V ∧ j ⁻¹' V = U := by
  let t : Y → X := fun y ↦ hj.toHomeomorph.symm ⟨k y, hr.symm ▸ Set.mem_range_self y⟩
  have ht : Continuous t := hj.toHomeomorph.symm.continuous.comp (hk.subtype_mk _)
  have hjt (y : Y) : j (t y) = k y :=
    congrArg Subtype.val (hj.toHomeomorph.apply_symm_apply _)
  obtain ⟨V, hV, he⟩ := hlift (t ⁻¹' U) (hU.preimage ht)
  refine ⟨V, hV, ?_⟩
  ext x
  obtain ⟨y, hy⟩ := hr ▸ Set.mem_range_self x
  have hty : t y = x := hj.injective ((hjt y).trans hy)
  change j x ∈ V ↔ x ∈ U
  rw [← hy, ← hty]
  exact Set.ext_iff.mp he y

/-! ### Closed subsets of the spectrum of a henselian pair -/

/-- A nonempty closed subset of `Spec A` meets the closed fibre `V(I)` of a henselian pair
`(A, I)`:  it contains a closed point, whose prime is maximal and therefore contains `I`, which
lies in the Jacobson radical. -/
private theorem exists_mem_zeroLocus_of_isClosed_of_henselianPair {A : Type u} [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {Z : Set (PrimeSpectrum A)} (hZ : IsClosed Z)
    (hne : Z.Nonempty) : ∃ p ∈ Z, p ∈ PrimeSpectrum.zeroLocus (I : Set A) := by
  obtain ⟨s, rfl⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus Z).mp hZ
  obtain ⟨p, hp⟩ := hne
  have hspan : Ideal.span s ≤ p.asIdeal := Ideal.span_le.mpr hp
  have hproper : Ideal.span s ≠ ⊤ := fun h ↦ p.isPrime.ne_top (top_le_iff.mp (h ▸ hspan))
  obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal (Ideal.span s) hproper
  have hIm : I ≤ m := by
    calc
      I ≤ (⊥ : Ideal A).jacobson := hI.le_jacobson
      _ = Ring.jacobson A := Ideal.jacobson_bot
      _ ≤ m := @Ring.jacobson_le_of_isMaximal A _ m hm
  exact ⟨⟨m, hm.isPrime⟩, Ideal.span_le.mp hsm, hIm⟩

/-- A closed set whose points over the closed fibre of a henselian pair lie in an open set is
contained in that open set:  otherwise the image of the difference is a nonempty closed subset of
`Spec A`, which must meet `V(I)`. -/
theorem subset_of_isClosed_of_forall_mem_zeroLocus {A : Type u} [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {X : Type*} [TopologicalSpace X]
    (f : X → PrimeSpectrum A) (hf : IsClosedMap f) {V O : Set X} (hV : IsClosed V)
    (hO : IsOpen O) (hc : ∀ x, f x ∈ PrimeSpectrum.zeroLocus (I : Set A) → x ∈ V → x ∈ O) :
    V ⊆ O := by
  intro x hx
  by_contra hxo
  obtain ⟨p, ⟨z, ⟨hzV, hzO⟩, hzp⟩, hp⟩ :=
    exists_mem_zeroLocus_of_isClosed_of_henselianPair I hI (hf _ (hV.sdiff hO))
      ⟨f x, x, ⟨hx, hxo⟩, rfl⟩
  exact hzO (hc z (hzp ▸ hp) hzV)

/-- The range of `Spec (A ⧸ I) ⟶ Spec A` is the closed fibre `V(I)`. -/
theorem range_spec_map_quotient_mk {A : Type u} [CommRing A] (I : Ideal A) :
    Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
  change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]

/-- **Lifting an open and closed subset along the quotient of an integral algebra.**  If `(A, I)`
is a henselian pair and `B` is an integral `A`-algebra, every open and closed subset of
`Spec (B ⧸ IB)` is the preimage of an open and closed subset of `Spec B`:  it is cut out by an
idempotent, which lifts to `B` by [Stacks, Tag 09XI]. -/
theorem exists_isClopen_preimage_eq_of_isIntegral_of_henselianPair (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) (B : Type u) [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] {U : Set (PrimeSpectrum (B ⧸ I.map (algebraMap A B)))}
    (hU : IsClopen U) :
    ∃ V : Set (PrimeSpectrum B), IsClopen V ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk (I.map (algebraMap A B))) ⁻¹' V = U := by
  obtain ⟨e, he, hEq⟩ := PrimeSpectrum.isClopen_iff.mp hU
  have hbij := ((henselianPair_tfae.{u, u} A I).out 1 4).mp hI
  obtain ⟨⟨b, hb⟩, hmk⟩ := (hbij B).2 ⟨e, he⟩
  refine ⟨PrimeSpectrum.basicOpen b, PrimeSpectrum.isClopen_iff.mpr ⟨b, hb, rfl⟩, ?_⟩
  rw [hEq]
  ext x
  change b ∉ (PrimeSpectrum.comap
    (Ideal.Quotient.mk (I.map (algebraMap A B))) x).asIdeal ↔ e ∉ x.asIdeal
  rw [PrimeSpectrum.comap_asIdeal]
  change Ideal.Quotient.mk (I.map (algebraMap A B)) b ∉ x.asIdeal ↔ e ∉ x.asIdeal
  rw [show Ideal.Quotient.mk _ b = e from congrArg Subtype.val hmk]

/-! ### Base change of a subscheme -/

/-- The morphism `W ×_S T ⟶ X ×_S T` induced by `w : W ⟶ X` over `S`, where `f : W ⟶ S` is the
composite `w ≫ h`. -/
noncomputable def pullbackMapOfFac {W X S T : Scheme.{u}} (w : W ⟶ X) (h : X ⟶ S) (f : W ⟶ S)
    (hw : w ≫ h = f) (q : T ⟶ S) : pullback f q ⟶ pullback h q :=
  pullback.lift (pullback.fst f q ≫ w) (pullback.snd f q)
    (by rw [Category.assoc, hw]; exact pullback.condition)

/-- Base change of a subscheme is a base change:  the square formed by `pullbackMapOfFac` and the
two first projections is cartesian over `w`. -/
theorem isPullback_pullbackMapOfFac {W X S T : Scheme.{u}} (w : W ⟶ X) (h : X ⟶ S) (f : W ⟶ S)
    (hw : w ≫ h = f) (q : T ⟶ S) :
    IsPullback (pullbackMapOfFac w h f hw q) (pullback.fst f q) (pullback.fst h q) w := by
  subst hw
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback h q).flip
  · simpa only [pullbackMapOfFac, pullback.lift_snd] using
      (IsPullback.of_hasPullback (w ≫ h) q).flip
  · exact pullback.lift_fst _ _ _

/-- The range of one leg of a cartesian square of schemes is the preimage of the range of the
opposite one. -/
private theorem range_eq_preimage_range_of_isPullback {P X Y S : Scheme.{u}} {a : P ⟶ X}
    {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} (hp : IsPullback a b f g) :
    Set.range a = f ⁻¹' Set.range g := by
  rw [← hp.isoPullback_hom_fst]
  change Set.range (pullback.fst f g ∘ hp.isoPullback.hom) = _
  rw [Set.range_comp, hp.isoPullback.hom.surjective.range_eq, Set.image_univ,
    Scheme.Pullback.range_fst]

/-! ### Lifting an open and closed subset off the closed fibre -/

/-- If `j` is injective, the range of `a` is the preimage under `j` of the range of `a ≫ j`. -/
private theorem range_eq_preimage_range_comp {P X Y : Scheme.{u}} (a : P ⟶ X) (j : X ⟶ Y)
    (hj : Function.Injective j) : Set.range a = j ⁻¹' Set.range (a ≫ j) := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hj.preimage_image]


/-- **Lifting an open and closed subset off the closed fibre of an integral morphism.**  If
`(A, I)` is a henselian pair and `h : T ⟶ Spec A` is integral, every open and closed subset of the
closed fibre `T ×_{Spec A} Spec (A ⧸ I)` is the restriction of an open and closed subset of
`T`. -/
theorem exists_isClopen_preimage_eq_of_isIntegralHom_of_henselianPair (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {T : Scheme.{u}} (h : T ⟶ Spec (.of A))
    [IsIntegralHom h]
    {U : Set ↥(pullback h (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))}
    (hU : IsClopen U) :
    ∃ V : Set T, IsClopen V ∧
      pullback.fst h (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹' V = U := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : IsClosedImmersion q :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsAffine T := isAffine_of_isAffineHom h
  let B := Γ(T, ⊤)
  let φ : CommRingCat.of A ⟶ B := Spec.preimage (T.isoSpec.inv ≫ h)
  have hφ : Spec.map φ = T.isoSpec.inv ≫ h := Spec.map_preimage _
  let : Algebra A B := φ.hom.toAlgebra
  have : IsIntegralHom (Spec.map φ) := hφ ▸ inferInstance
  have : Algebra.IsIntegral A B := ⟨IsIntegralHom.SpecMap_iff.mp ‹_›⟩
  let j := pullback.fst h q ≫ T.isoSpec.hom
  have hr : Set.range j =
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I.map (algebraMap A B)))) := by
    change Set.range (T.isoSpec.hom ∘ pullback.fst h q) = _
    rw [Set.range_comp, Scheme.Pullback.range_fst,
      show Set.range q = PrimeSpectrum.zeroLocus (I : Set A) from range_spec_map_quotient_mk I,
      range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    ext b
    constructor
    · rintro ⟨t, ht, rfl⟩
      change I.map φ.hom ≤ (T.isoSpec.hom t).asIdeal
      rw [Ideal.map_le_iff_le_comap]
      change I ≤ (PrimeSpectrum.comap φ.hom (T.isoSpec.hom t)).asIdeal
      have hh : (Spec.map φ) (T.isoSpec.hom t) = h t := by
        rw [hφ]
        simp
      change I ≤ (h t).asIdeal at ht
      rw [← hh] at ht
      exact ht
    · intro hb
      refine ⟨T.isoSpec.inv b, ?_, by simp⟩
      change I ≤ (h (T.isoSpec.inv b)).asIdeal
      have hh : h (T.isoSpec.inv b) = PrimeSpectrum.comap φ.hom b := by
        change (T.isoSpec.inv ≫ h) b = (Spec.map φ) b
        rw [hφ]
      rw [hh]
      exact Ideal.map_le_iff_le_comap.mp hb
  obtain ⟨V, hV, he⟩ := exists_isClopen_preimage_eq_of_range_eq j
    (PrimeSpectrum.comap (Ideal.Quotient.mk (I.map (algebraMap A B)))) j.isEmbedding
    (PrimeSpectrum.continuous_comap _) hr
    (fun _ hW ↦ exists_isClopen_preimage_eq_of_isIntegral_of_henselianPair A I hI B hW) hU
  exact ⟨T.isoSpec.hom ⁻¹' V, hV.preimage T.isoSpec.hom.continuous, he⟩

/-- **Lifting an open and closed subset off the closed fibre of a proper morphism.**  If `(A, I)`
is a henselian pair and `f : X ⟶ Spec A` is proper with geometrically connected Stein fibres,
every open and closed subset of the closed fibre `X ×_{Spec A} Spec (A ⧸ I)` is the restriction of
an open and closed subset of `X`.

The Stein factorization `X ⟶ f.normalization ⟶ Spec A` has proper first factor and integral
second factor, so the subset is pushed forward along the base change of the first factor — which
is legitimate because its fibres are connected — and lifted along the second factor by
`AlgebraicGeometry.exists_isClopen_preimage_eq_of_isIntegralHom_of_henselianPair`. -/
theorem exists_isClopen_preimage_eq_of_isProper_of_henselianPair (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    [GeometricallyConnected f.toNormalization]
    {U : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))}
    (hU : IsClopen U) :
    ∃ V : Set X, IsClopen V ∧
      pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹' V = U := by
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let g := f.toNormalization
  let h := f.fromNormalization
  have hgf : g ≫ h = f := Scheme.Hom.toNormalization_fromNormalization f
  have hgc : GeometricallyConnected g := ‹GeometricallyConnected f.toNormalization›
  have hgp : IsProper g := Stacks.SteinFactorization.isProper_toNormalization f
  let g₀ := pullbackMapOfFac g h f hgf q
  have hg₀ := isPullback_pullbackMapOfFac g h f hgf q
  have : IsProper g₀ := MorphismProperty.of_isPullback hg₀.flip hgp
  have : GeometricallyConnected g₀ := MorphismProperty.of_isPullback hg₀.flip hgc
  obtain ⟨himage, hpre⟩ := isClopen_image_and_preimage_image_eq g₀ g₀.isClosedMap g₀.surjective
    (fun z ↦ (g₀.isConnected_preimage_singleton z).isPreconnected) hU
  obtain ⟨V, hV, he⟩ :=
    exists_isClopen_preimage_eq_of_isIntegralHom_of_henselianPair A I hI h himage
  refine ⟨g ⁻¹' V, hV.preimage g.continuous, ?_⟩
  have hc : g₀ ≫ pullback.fst h q = pullback.fst f q ≫ g := pullback.lift_fst _ _ _
  ext x
  change g (pullback.fst f q x) ∈ V ↔ x ∈ U
  rw [← Scheme.Hom.comp_apply, ← hc]
  change g₀ x ∈ pullback.fst h q ⁻¹' V ↔ x ∈ U
  rw [he]
  exact Set.ext_iff.mp hpre x

/-! ### The proper part of the closed fibre -/

/-- **[Stacks, Tag 0CT9] with [Stacks, Tag 0F41] carried as `hcpt` and clause (1) of
[Stacks, Tag 03H2] carried as `hconn`.**

Let `(A, I)` be a henselian pair and let `f : X ⟶ Spec A` be separated and of finite type.  An
open and closed subscheme `i : Y ⟶ X ×_{Spec A} Spec (A ⧸ I)` of the closed fibre which is proper
over `Spec (A ⧸ I)` is the closed fibre of an open and closed subscheme `w : W ⟶ X` which is
proper over `Spec A`.

Choosing a compactification `X ⟶ P ⟶ Spec A` of `f`, the image of `Y` in the closed fibre of `P`
is open and closed and lifts to an open and closed subset `V` of `P`.  Since the points of `V`
over the closed fibre lie in `X`, all of `V` does, and `V` cuts out the required subscheme of
`X`.

The tag's hypotheses and its full conclusion are exactly those below.  The two extra arguments
are the conclusions of other tags, quoted by the source and unavailable here:  `hcpt` is
Nagata's compactification theorem, Tag 0F41, and `hconn` is the connectedness conjunct of clause
(1) of Tag 03H2, which rests on Tag 0G7X and hence on Tags 02OC and 02OB.  The quantifier on
`hconn` is forced by `hcpt` being an existential:  the connectedness input is applied to the
compactification `P`, which is produced rather than given.  The source reaches the same
reduction through Chow's lemma (Tag 0202) and Tag 01RG instead of through Tag 0F41; that route
is equally unavailable, Tag 0202 being conditional here on
`Scheme.FiniteTypeApproximation.IsOneAffineOpenStep`. -/
@[stacks 0CT9 "the whole statement, with two inputs the source quotes carried as named
hypotheses: `hcpt`, Nagata compactification (Stacks 0F41), and `hconn`, the connectedness
conjunct of clause (1) of Stacks 03H2 (through Stacks 0G7X, 02OC and 02OB); neither is proved in
this repository, and neither is any part of this tag's own conclusion"]
theorem exists_isClopen_isProper_of_henselianPair_of_compactification (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (hcpt : ∃ (P : Scheme.{u}) (j : X ⟶ P) (π : P ⟶ Spec (.of A)),
      IsOpenImmersion j ∧ IsProper π ∧ j ≫ π = f)
    (hconn : ∀ {P : Scheme.{u}} (π : P ⟶ Spec (.of A)) [IsProper π],
      GeometricallyConnected π.toNormalization)
    {Y : Scheme.{u}}
    (i : Y ⟶ pullback f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    [IsOpenImmersion i] [IsClosedImmersion i]
    [IsProper (i ≫ pullback.snd f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))] :
    ∃ (W : Scheme.{u}) (w : W ⟶ X) (_ : IsOpenImmersion w) (_ : IsClosedImmersion w)
      (_ : IsProper (w ≫ f)),
      let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      let w₀ : pullback (w ≫ f) q ⟶ pullback f q :=
        pullback.lift (pullback.fst (w ≫ f) q ≫ w) (pullback.snd (w ≫ f) q)
          (by rw [Category.assoc]; exact pullback.condition)
      ∃ e : Y ≅ pullback (w ≫ f) q, e.hom ≫ w₀ = i := by
  classical
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  obtain ⟨P, j, π, hjo, hπp, hj⟩ := hcpt
  have : IsOpenImmersion j := hjo
  have : IsProper π := hπp
  have : GeometricallyConnected π.toNormalization := hconn π
  -- The image of `Y` in the closed fibre of `P` is open and closed.
  let j₀ := pullbackMapOfFac j π f hj q
  have hj₀ := isPullback_pullbackMapOfFac j π f hj q
  have : IsOpenImmersion j₀ := MorphismProperty.of_isPullback hj₀.flip ‹IsOpenImmersion j›
  have hj₀s : j₀ ≫ pullback.snd π q = pullback.snd f q := pullback.lift_snd _ _ _
  have : IsProper ((i ≫ j₀) ≫ pullback.snd π q) := by
    rw [Category.assoc, hj₀s]
    infer_instance
  have : IsProper (i ≫ j₀) := IsProper.of_comp _ (pullback.snd π q)
  have hU : IsClopen (Set.range (i ≫ j₀)) :=
    ⟨(i ≫ j₀).isClosedMap.isClosed_range, (i ≫ j₀).isOpenEmbedding.isOpen_range⟩
  obtain ⟨V, hV, hV₀⟩ := exists_isClopen_preimage_eq_of_isProper_of_henselianPair A I hI π hU
  -- All of `V` lies in `X`, because its points over the closed fibre do.
  have hVj : V ⊆ Set.range j := by
    refine subset_of_isClosed_of_forall_mem_zeroLocus I hI π π.isClosedMap hV.isClosed
      j.isOpenEmbedding.isOpen_range fun x hx hxV ↦ ?_
    obtain ⟨x₀, hx₀⟩ : x ∈ Set.range (pullback.fst π q) := by
      rw [Scheme.Pullback.range_fst]
      rwa [range_spec_map_quotient_mk I]
    have hx₀V : x₀ ∈ pullback.fst π q ⁻¹' V := by
      change pullback.fst π q x₀ ∈ V
      rwa [hx₀]
    rw [hV₀] at hx₀V
    obtain ⟨y, hy⟩ := hx₀V
    refine ⟨pullback.fst f q (i y), ?_⟩
    calc
      j (pullback.fst f q (i y)) = pullback.fst π q (j₀ (i y)) :=
        (congrArg (fun k : pullback f q ⟶ P ↦ k (i y)) hj₀.w).symm
      _ = x := by
        change pullback.fst π q ((i ≫ j₀) y) = x
        rw [hy, hx₀]
  -- Cut `V` down to an open and closed subscheme of `X`.
  obtain ⟨W, v, hvOpen, hvClosed, hv⟩ := exists_isOpenImmersion_isClosedImmersion_range_eq hV
  have : IsOpenImmersion v := hvOpen
  have hvj : Set.range v ⊆ Set.range j := hv ▸ hVj
  let w := IsOpenImmersion.lift j v hvj
  have hwj : w ≫ j = v := IsOpenImmersion.lift_fac j v hvj
  have hwRange : Set.range w = j ⁻¹' V := by
    rw [range_eq_preimage_range_comp w j j.isOpenEmbedding.injective, hwj, hv]
  have : IsClosedImmersion w :=
    IsClosedImmersion.of_isPreimmersion w (hwRange ▸ hV.isClosed.preimage j.continuous)
  have : IsProper (w ≫ f) := by
    rw [← hj, ← Category.assoc, hwj]
    infer_instance
  refine ⟨W, w, inferInstance, inferInstance, inferInstance, ?_⟩
  change ∃ e : Y ≅ pullback (w ≫ f) q, e.hom ≫ pullbackMapOfFac w f (w ≫ f) rfl q = i
  have : IsOpenImmersion (pullbackMapOfFac w f (w ≫ f) rfl q) :=
    MorphismProperty.of_isPullback (isPullback_pullbackMapOfFac w f (w ≫ f) rfl q).flip
      inferInstance
  have hr : Set.range i = Set.range (pullbackMapOfFac w f (w ≫ f) rfl q) := by
    rw [range_eq_preimage_range_of_isPullback (isPullback_pullbackMapOfFac w f (w ≫ f) rfl q),
      hwRange]
    rw [range_eq_preimage_range_comp i j₀ j₀.isOpenEmbedding.injective, ← hV₀]
    ext x₀
    change j₀ x₀ ∈ pullback.fst π q ⁻¹' V ↔ j (pullback.fst f q x₀) ∈ V
    rw [← Scheme.Hom.comp_apply, ← hj₀.w]
    rfl
  exact ⟨IsOpenImmersion.isoOfRangeEq i (pullbackMapOfFac w f (w ≫ f) rfl q) hr,
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

end AlgebraicGeometry

end
