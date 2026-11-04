module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties
public import StacksCore.Tactic.StacksAttribute

/-!
# Dominance and generic points

A scheme is a sober space, so each of its irreducible components has a generic point, and the
closure of the set of all such points is the whole scheme. Dominance of a morphism can therefore
be tested on generic points alone, and this file records the three forms that test takes.

The quasi-compact case is the sharp one: a quasi-compact morphism is dominant as soon as its
image *contains* the generic points of the target, with no closure needed. The key geometric
input is that a generic point outside the image of a quasi-compact morphism can be separated
from that image by an open neighbourhood with empty inverse image; this is proved by passing to
an affine neighbourhood, where the generic point becomes a minimal prime and minimal primes in
the closure of the image of a ring map are hit by that map.

Without quasi-compactness one still has the test over a source with finitely many irreducible
components, and dominance transports that finiteness to the target.

## Main results

* `AlgebraicGeometry.exists_open_nhds_disjoint_range_of_quasiCompact`: a generic point missing
  the image of a quasi-compact morphism has an open neighbourhood with empty inverse image.
* `AlgebraicGeometry.isDominant_iff_genericPoints_subset_range`: a quasi-compact morphism is
  dominant exactly when its image contains the generic points of the target.
* `AlgebraicGeometry.isDominant_iff_genericPoint_mem_range`: the same test for a source with
  finitely many irreducible components.
* `AlgebraicGeometry.finite_irreducibleComponents_of_isDominant`: a dominant morphism carries
  finiteness of the set of irreducible components from its source to its target.
* `AlgebraicGeometry.iUnion_closure_image_genericPoints_eq_univ`: the closures of the images of
  chosen generic points of the source cover the target.

## Implementation notes

Mathlib's `genericPoints S` is the set of generic points of the irreducible components of `S`,
so inclusion in the range of the underlying map states the condition without choosing a generic
point for each component. Where a choice is wanted instead, an irreducible component is treated
as an element of `irreducibleComponents S` and its generic point is the canonical point supplied
by sobriety.

## References

* [Stacks Project, Tag 01RL](https://stacks.math.columbia.edu/tag/01RL)
* [Stacks Project, Tag 01RM](https://stacks.math.columbia.edu/tag/01RM)
* [Stacks Project, Tag 02NE](https://stacks.math.columbia.edu/tag/02NE)
-/

@[expose] public section

open CategoryTheory Set TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Separating a generic point from the image of a quasi-compact morphism -/

section QuasiCompact

/-- A minimal prime in the closure of the image of `PrimeSpectrum.comap` lies in that image:
the closure condition puts it in the zero locus of the kernel, where minimality lets it be
lifted. -/
private theorem minPoint_range {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : PrimeSpectrum A)
    (hp : p.asIdeal ∈ minimalPrimes A)
    (hcl : p ∈ closure (Set.range (PrimeSpectrum.comap φ))) :
    p ∈ Set.range (PrimeSpectrum.comap φ) := by
  rw [PrimeSpectrum.closure_range_comap] at hcl
  have hmin : p.asIdeal ∈ (RingHom.ker φ).minimalPrimes := by
    simp only [Set.mem_ofPred, Ideal.IsMinimalPrime] at hp ⊢
    exact ⟨⟨hp.1.1, (PrimeSpectrum.mem_zeroLocus p _).mp hcl⟩,
      fun q hq hqle => hp.2 ⟨hq.1, bot_le⟩ hqle⟩
  obtain ⟨q, hq, _, hqeq⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes φ p.asIdeal hmin
  exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqeq⟩

/-- An irreducible component contained in the closure of a point is that closure: the closure is
irreducible and the component is maximal. -/
private theorem closure_singleton_eq_of_subset {S : Type*} [TopologicalSpace S]
    {T : Set S} (hT : T ∈ irreducibleComponents S) {y : S} (h : T ⊆ closure ({y} : Set S)) :
    closure ({y} : Set S) = T :=
  (hT.2 isIrreducible_singleton.closure h).antisymm h

/-- A generic point of an irreducible component specializing from a point is that point: both
closures are irreducible and maximal, hence equal. -/
private theorem eq_of_genericPoint_mem_closure_singleton {S : Type*} [TopologicalSpace S]
    [T0Space S] {η y : S} (hη : η ∈ genericPoints S)
    (hy : η ∈ closure ({y} : Set S)) : y = η := by
  have hC : closure ({η} : Set S) ∈ irreducibleComponents S := hη
  have hsub : closure ({η} : Set S) ⊆ closure ({y} : Set S) :=
    closure_minimal (by simpa using hy) isClosed_closure
  have hsub' : closure ({y} : Set S) ⊆ closure ({η} : Set S) :=
    (closure_singleton_eq_of_subset hC hsub).le
  exact (inseparable_iff_specializes_and.2 ⟨specializes_iff_mem_closure.mpr hy,
    specializes_iff_mem_closure.mpr (hsub' (subset_closure (Set.mem_singleton y)))⟩).eq

/-- A generic point of an irreducible component admits no proper generalization. -/
private theorem stableUnderGeneralization_singleton_of_mem_genericPoints {S : Type*}
    [TopologicalSpace S] [T0Space S] {η : S} (hη : η ∈ genericPoints S) :
    StableUnderGeneralization ({η} : Set S) := by
  intro x y hy hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  exact Set.mem_singleton_iff.mpr
    (eq_of_genericPoint_mem_closure_singleton hη (specializes_iff_mem_closure.mp hy))

/-- The spectral form of `minPoint_range`, for a morphism of affine schemes presented as
`Spec.map` of a ring map. -/
private theorem specMap_minPoint_range {A B : CommRingCat} (φ : A ⟶ B)
    (p : Spec A) (hp : p.asIdeal ∈ minimalPrimes A)
    (hcl : p ∈ closure (Set.range (Spec.map φ))) :
    p ∈ Set.range (Spec.map φ) := by
  change (p : PrimeSpectrum A) ∈
    closure (Set.range (PrimeSpectrum.comap φ.hom)) at hcl
  exact minPoint_range φ.hom p hp hcl

/-- A generic point of the target lying in an affine open corresponds to a minimal prime of the
ring of sections. -/
private theorem isoSpec_mem_minimalPrimes_of_mem_genericPoints {S : Scheme} {U : S.Opens}
    (hU : IsAffineOpen U) {η : S} (hη : η ∈ genericPoints S) (hηU : η ∈ U) :
    (hU.isoSpec.hom ⟨η, hηU⟩).asIdeal ∈ minimalPrimes Γ(S, U) := by
  let ηU : (↑U : Scheme) := ⟨η, hηU⟩
  let p : Spec Γ(S, U) := hU.isoSpec.hom ηU
  have hpStable : StableUnderGeneralization ({p} : Set (PrimeSpectrum Γ(S, U))) := by
    intro x y hy hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    have hyU : hU.isoSpec.inv y ⤳ ηU := by
      simpa [p] using hy.map (Scheme.Hom.continuous hU.isoSpec.inv)
    have hyS : U.ι (hU.isoSpec.inv y) ⤳ η := hyU.map (Scheme.Hom.continuous U.ι)
    have hyEtaU : hU.isoSpec.inv y = ηU :=
      Subtype.ext (stableUnderGeneralization_singleton_of_mem_genericPoints hη hyS rfl)
    refine hU.isoSpec.schemeIsoToHomeo.symm.injective ?_
    show hU.isoSpec.inv y = hU.isoSpec.inv p
    simpa [p] using hyEtaU
  exact PrimeSpectrum.stableUnderGeneralization_singleton.mp hpStable

/-- Over an affine open `U`, a point of `U` given by a minimal prime of `Γ(S, U)` that lies in
the closure of the image of a morphism from an affine scheme lies in that image. -/
private theorem mem_range_of_mem_closure_of_isAffineOpen {S : Scheme} {U : S.Opens}
    (hU : IsAffineOpen U) {R : CommRingCat} (l : Spec R ⟶ (↑U : Scheme)) (y : (↑U : Scheme))
    (hy : (hU.isoSpec.hom y).asIdeal ∈ minimalPrimes Γ(S, U))
    (hcl : y ∈ closure (Set.range l)) : y ∈ Set.range l := by
  let p : Spec Γ(S, U) := hU.isoSpec.hom y
  let hAffine : Spec R ⟶ Spec Γ(S, U) := l ≫ hU.isoSpec.hom
  have hAffineRange : Set.range hAffine = hU.isoSpec.hom '' Set.range l := by
    rw [← Set.range_comp]
    rfl
  have hpCl : p ∈ closure (Set.range hAffine) := by
    rw [hAffineRange]
    exact (image_closure_subset_closure_image
      (f := hU.isoSpec.hom) hU.isoSpec.hom.continuous) ⟨y, hcl, rfl⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective hAffine
  obtain ⟨x, hx⟩ := specMap_minPoint_range ψ p hy (by rwa [hψ])
  have hxAffine : hAffine x = p := by rwa [← hψ]
  have hx' : hU.isoSpec.hom (l x) = hU.isoSpec.hom y := by
    simpa [hAffine, p] using hxAffine
  refine ⟨x, hU.isoSpec.schemeIsoToHomeo.injective ?_⟩
  show Scheme.homeoOfIso hU.isoSpec (l x) = Scheme.homeoOfIso hU.isoSpec y
  rwa [Scheme.homeoOfIso_apply]

/-- A generic point of an irreducible component of the target lying in the closure of the image
of a quasi-compact morphism already lies in that image.

The point is pulled into an affine open `U` of the target, where it is a minimal prime of
`Γ(S, U)` because it admits no proper generalization. Quasi-compactness makes the inverse image
of `U` the image of an affine scheme, so the situation becomes a ring map whose image has the
minimal prime in its closure, and `minPoint_range` applies. -/
private theorem qc_genericPoint_mem_range_of_mem_closure
    {X S : Scheme} (f : X ⟶ S) [QuasiCompact f]
    (η : S) (hη : η ∈ genericPoints S)
    (hηcl : η ∈ closure (Set.range f)) :
    η ∈ Set.range f := by
  let i := S.affineCover.idx η
  let U : S.Opens := (S.affineCover.f i).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (S.affineCover.f i)
  have hηU : η ∈ U := by
    simpa [U] using S.affineCover.covers η
  obtain ⟨R, g, hg⟩ :=
    (isCompact_iff_exists (U := f ⁻¹ᵁ U)).mp (f.isCompact_preimage hU.isCompact)
  let h : Spec R ⟶ S := g ≫ f
  have hrange : Set.range h = Set.range f ∩ (U : Set S) := by
    show Set.range (f ∘ g) = _
    rw [Set.range_comp, hg]
    show f '' (f ⁻¹' (U : Set S)) = _
    simpa only [Set.inter_comm] using (Set.image_preimage_eq_inter_range (f := f) (t := U))
  have hηhcl : η ∈ closure (Set.range h) := by
    rw [hrange]
    exact U.isOpen.closure_inter ⟨hηcl, hηU⟩
  have hsub : Set.range h ⊆ Set.range U.ι := by
    rw [hrange]
    exact fun z hz => ⟨⟨z, hz.2⟩, rfl⟩
  let l : Spec R ⟶ (↑U : Scheme) := IsOpenImmersion.lift U.ι h hsub
  have hlift : l ≫ U.ι = h := IsOpenImmersion.lift_fac U.ι h hsub
  have hImage : U.ι '' Set.range l = Set.range h := by
    rw [← Set.range_comp]
    show Set.range (l ≫ U.ι) = Set.range h
    rw [hlift]
  have hηUcl : (⟨η, hηU⟩ : (↑U : Scheme)) ∈ closure (Set.range l) := by
    rw [U.ι.isOpenEmbedding.toIsEmbedding.closure_eq_preimage_closure_image]
    show U.ι ⟨η, hηU⟩ ∈ closure (U.ι '' Set.range l)
    rwa [hImage]
  obtain ⟨x, hx⟩ := mem_range_of_mem_closure_of_isAffineOpen hU l ⟨η, hηU⟩
    (isoSpec_mem_minimalPrimes_of_mem_genericPoints hU hη hηU) hηUcl
  refine ⟨g x, ?_⟩
  calc
    f (g x) = h x := rfl
    _ = (l ≫ U.ι) x := by rw [hlift]
    _ = U.ι (l x) := rfl
    _ = U.ι ⟨η, hηU⟩ := congrArg U.ι hx
    _ = η := rfl

/-- **Stacks Project, Tag 02NE.** If a generic point of an irreducible
component is not in the image of a quasi-compact morphism of schemes, it has
an open neighbourhood with empty inverse image. -/
@[stacks 02NE, ega "IV 9.7.5.1" "more general"]
theorem exists_open_nhds_disjoint_range_of_quasiCompact
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (η : S) (hη : η ∈ genericPoints S) (hηf : η ∉ Set.range f) :
    ∃ V : S.Opens, η ∈ V ∧ f ⁻¹ᵁ V = ⊥ := by
  let V : S.Opens := ⟨(closure (Set.range f))ᶜ, isClosed_closure.isOpen_compl⟩
  refine ⟨V, fun hηcl => hηf (qc_genericPoint_mem_range_of_mem_closure f η hη hηcl), ?_⟩
  rw [eq_bot_iff]
  intro x hx
  have hxV : f x ∉ closure (Set.range f) := by
    simpa [Scheme.Hom.mem_preimage, V, Set.mem_compl_iff] using hx
  exact (hxV (subset_closure ⟨x, rfl⟩)).elim

/-- **Stacks Project, Tag 01RL.** A quasi-compact morphism of schemes is dominant if and only if
its image contains every generic point of an irreducible component of the target. -/
@[stacks 01RL, ega "IV 1.1.5" "a) <=> b)", ega "I 6.6.5"]
theorem isDominant_iff_genericPoints_subset_range {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] :
    IsDominant f ↔ genericPoints S ⊆ Set.range f := by
  rw [isDominant_iff, DenseRange]
  constructor
  · intro hf η hη
    by_contra hηf
    obtain ⟨V, hV, hVpre⟩ := exists_open_nhds_disjoint_range_of_quasiCompact f η hη hηf
    obtain ⟨_, hx, y, rfl⟩ := hf.inter_open_nonempty V V.2 ⟨η, hV⟩
    simpa [hVpre] using (show y ∈ f ⁻¹ᵁ V from hx)
  · exact fun hf => (dense_iff_closure_eq.mpr genericPoints.closure).mono hf

end QuasiCompact

/-! ### Sources with finitely many irreducible components -/

/-- If a dominant morphism of schemes has only finitely many irreducible components, then the
closures of the images of chosen generic points of those components cover the target. -/
theorem iUnion_closure_image_genericPoints_eq_univ
    {X S : Scheme.{u}} (f : X ⟶ S) [IsDominant f]
    (hfinite : (irreducibleComponents X).Finite)
    (ξ : irreducibleComponents X → X)
    (hξ : ∀ Z, IsGenericPoint (ξ Z) (Z : Set X)) :
    (⋃ Z : irreducibleComponents X, closure ({f (ξ Z)} : Set S)) = Set.univ := by
  have : Finite (irreducibleComponents X) := hfinite.to_subtype
  have hrange : Set.range f ⊆ ⋃ Z : irreducibleComponents X, closure ({f (ξ Z)} : Set S) := by
    rintro _ ⟨x, rfl⟩
    have hxcover : x ∈ ⋃ Z : irreducibleComponents X, (Z : Set X) := by
      rw [← sUnion_eq_iUnion, sUnion_irreducibleComponents]
      trivial
    obtain ⟨(Z : irreducibleComponents X), hZ⟩ := Set.mem_iUnion.mp hxcover
    have hxZ : x ∈ closure ({ξ Z} : Set X) := by rwa [hξ Z]
    exact Set.mem_iUnion.2 ⟨Z, by simpa using mem_closure_image f.continuous.continuousAt hxZ⟩
  exact Set.eq_univ_of_forall fun y =>
    closure_minimal hrange (isClosed_iUnion_of_finite fun _ => isClosed_closure) (f.denseRange y)

/-- The closures of the images of the generic points of the finitely many irreducible components
of the source of a dominant morphism cover the target. -/
private theorem iUnion_closure_genericPoint_eq_univ
    {X S : Scheme.{u}} (f : X ⟶ S) [IsDominant f] (hfinite : (irreducibleComponents X).Finite) :
    (⋃ Z : irreducibleComponents X, closure ({f Z.2.1.genericPoint} : Set S)) = Set.univ :=
  iUnion_closure_image_genericPoints_eq_univ f hfinite _
    fun Z => Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)

/-- **Stacks Project, Tag 01RM.** A morphism from a scheme with finitely many irreducible
components is dominant if and only if its image contains the generic point of every irreducible
component of the target. -/
@[stacks 01RM "dominant_iff_generic_points_in_image"]
lemma isDominant_iff_genericPoint_mem_range
    {X S : Scheme.{u}} (f : X ⟶ S)
    [Finite (irreducibleComponents X)] :
      IsDominant f ↔
      ∀ Z : irreducibleComponents S, Z.2.1.genericPoint ∈ Set.range f := by
  classical
  constructor
  · intro hdom Z
    obtain ⟨W, hW⟩ := Set.mem_iUnion.mp
      (show Z.2.1.genericPoint ∈ ⋃ W : irreducibleComponents X,
        closure ({f W.2.1.genericPoint} : Set S) by
          simp [iUnion_closure_genericPoint_eq_univ f (irreducibleComponents X).toFinite])
    have hsub : (Z : Set S) ⊆ closure ({f W.2.1.genericPoint} : Set S) :=
      ((genericPoints.isGenericPoint_ofComponent Z).mem_closed_set_iff
        isClosed_closure).mp hW
    exact ⟨W.2.1.genericPoint, (closure_singleton_eq_of_subset Z.2 hsub ▸ isGenericPoint_closure).eq
      (genericPoints.isGenericPoint_ofComponent Z)⟩
  · intro himg
    rw [isDominant_iff, denseRange_iff_closure_range]
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoints.closure]
    apply closure_mono
    intro x hx
    have h := himg (genericPoints.component ⟨x, hx⟩)
    change (genericPoints.ofComponent (genericPoints.component ⟨x, hx⟩)).1 ∈
      Set.range f at h
    simpa using h

/-- A dominant morphism of schemes with finitely many irreducible components in its source has
finitely many irreducible components in its target. -/
@[stacks 01RM "finite_irreducible_components_target"]
theorem finite_irreducibleComponents_of_isDominant
    {X S : Scheme.{u}} (f : X ⟶ S) [IsDominant f]
    (hX : (irreducibleComponents X).Finite) :
    (irreducibleComponents S).Finite := by
  classical
  have : Finite (irreducibleComponents X) := hX.to_subtype
  let C : irreducibleComponents X → Set S := fun Z => closure {f Z.2.1.genericPoint}
  have hfin : (Set.range C).Finite := Set.finite_range C
  apply hfin.subset
  intro T hT
  obtain ⟨U, hU, hTU⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hT.1 hfin.toFinset
      (by
        rintro U hU
        obtain ⟨Z, rfl⟩ := hfin.mem_toFinset.mp hU
        exact isClosed_closure)
      (by
        rw [hfin.coe_toFinset, Set.sUnion_range,
          show (⋃ Z, C Z) = Set.univ from iUnion_closure_genericPoint_eq_univ f hX]
        exact Set.subset_univ _)
  obtain ⟨Z, rfl⟩ := hfin.mem_toFinset.mp hU
  exact ⟨Z, closure_singleton_eq_of_subset hT hTU⟩

end AlgebraicGeometry
