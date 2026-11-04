module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of a formal spectrum over a basic open

For `f` in a pre-admissible topological ring `A` the open `D(f) ∩ Spf A` of the formal spectrum
has ring of sections `Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}} = lim_λ (A/I_λ)_f`, the limit of the
localizations at `f` of the quotients by the ideals of definition, each carrying the discrete
topology.

## Main definitions

* `AlgebraicGeometry.spfBasicOpen`: the open `D(f) ∩ Spf A` of the formal spectrum.
* `AlgebraicGeometry.spfAwayMapOn` and `AlgebraicGeometry.spfAwayDiagramOn`: the inverse system
  `λ ↦ (A/I_λ)_f` of discrete topological rings whose limit is `A_{\{f\}}`.
* `AlgebraicGeometry.spfAwayEquivOn`: the identification of the sections of `𝒪_λ` over
  `D(f) ∩ Spf A` with the localization `(A/I_λ)_f`.

## Main results

* `AlgebraicGeometry.isCompact_spfBasicOpen_of_isWeaklyPreAdmissible`: the open `D(f) ∩ Spf A`
  is quasi-compact, so the sections of each `𝒪_λ` over it are discrete.
* `AlgebraicGeometry.isLocalization_spfComponentOn_spfBasicOpen`: the sections of `𝒪_λ` over
  `D(f) ∩ Spf A` are the localization of `A/I_λ` away from the image of `f`.
* `AlgebraicGeometry.spfBasicOpenIsoOn`: the isomorphism
  `Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = lim_λ (A/I_λ)_f` as topological rings.

## Implementation notes

The open `D(f) ∩ Spf A` pulls back along the identification of `Spec (A/I_λ)` with `Spf A` to the
basic open of the image of `f` in `A/I_λ`, and definitionally so, which is what makes the
localization instances of the structure sheaf of an affine scheme apply directly here. Only
pre-admissibility is used: completeness of `A` plays no role in identifying the sections over a
basic open, but is what makes the resulting ring `A_{\{f\}}` admissible in turn.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Section 87.2 (Tag 0AHY)](https://stacks.math.columbia.edu/tag/0AHY)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace AlgebraicGeometry

open TopologicalRing

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-! ### The basic opens of a formal spectrum -/

/-- The open `D(f) ∩ Spf A` of the formal spectrum of `A`: the open primes of `A` not containing
`f`, an open subset of `Spf A` because `D(f)` is open in `Spec A`. -/
@[ega "I 10.1.4"]
def spfBasicOpen (f : A) : Opens (spfSpace A) :=
  ⟨Subtype.val ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum A)),
    (PrimeSpectrum.basicOpen f).isOpen.preimage continuous_subtype_val⟩

omit [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- A point of the formal spectrum lies in `D(f) ∩ Spf A` exactly when the corresponding open
prime does not contain `f`. -/
theorem mem_spfBasicOpen (f : A) (p : openPrimes A) :
    p ∈ (spfBasicOpen A f).carrier ↔ f ∉ p.1.asIdeal := Iff.rfl

omit [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- For `f = 1` the open `D(f) ∩ Spf A` is the whole formal spectrum, since no prime contains a
unit. -/
theorem spfBasicOpen_one : spfBasicOpen A 1 = ⊤ :=
  Opens.ext (Set.eq_univ_of_forall fun p => (mem_spfBasicOpen A 1 p).2 fun hp =>
    p.1.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp isUnit_one))

/-- Under the identification of `Spec (A/I)` with `Spf A` the open `D(f) ∩ Spf A` corresponds to
the basic open of the image of `f` in `A/I`: a prime of `A/I` avoids that image exactly when its
preimage in `A` avoids `f`. -/
@[ega "I 10.2.1" "Quotient case"]
theorem spfBasicOpen_preimage_spfOfQuotientOn (f : A) (I : SpfIndex A P) :
    (Opens.map (spfOfQuotientOn A I)).obj (spfBasicOpen A f)
      = PrimeSpectrum.basicOpen (Ideal.Quotient.mk I.1 f) := rfl

/-- Under the identification of `Spec (A/I)` with `Spf A` the open `D(f) ∩ Spf A` corresponds to
the basic open of the image of `f` in `A/I`: a prime of `A/I` avoids that image exactly when its
preimage in `A` avoids `f`.

The ideals-of-definition case of `spfBasicOpen_preimage_spfOfQuotientOn`. -/
@[ega "I 10.2.1" "Quotient case"]
theorem spfBasicOpen_preimage (f : A) (I : IdealsOfDefinition A) :
    (Opens.map (spfOfQuotient A I)).obj (spfBasicOpen A f)
      = PrimeSpectrum.basicOpen (Ideal.Quotient.mk I.1 f) :=
  spfBasicOpen_preimage_spfOfQuotientOn (A := A) (P := IsIdealOfDefinition) (f := f) (I := I)

/-- The open `D(f) ∩ Spf A` of the formal spectrum of a weakly pre-admissible topological ring is
quasi-compact: it is the preimage of the quasi-compact `D(f) ⊆ Spec A` under the closed embedding
of the space of open primes in `Spec A`. -/
@[ega "I 1.1.10" "more general"]
theorem isCompact_spfBasicOpen_of_isWeaklyPreAdmissible (hA : IsWeaklyPreAdmissible A) (f : A) :
    IsCompact ((spfBasicOpen A f : Opens (spfSpace A)) : Set (spfSpace A)) :=
  have hclosed := isClosed_openPrimes_of_isWeaklyPreAdmissible A hA
  hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (PrimeSpectrum.isCompact_basicOpen f)

/-- The open `D(f) ∩ Spf A` of the formal spectrum of a pre-admissible topological ring is
quasi-compact: it is the preimage of the quasi-compact `D(f) ⊆ Spec A` under the closed embedding
of `Spf A` in `Spec A`.

The ideals-of-definition case of `isCompact_spfBasicOpen_of_isWeaklyPreAdmissible`. -/
theorem isCompact_spfBasicOpen (hA : IsPreAdmissible A) (f : A) :
    IsCompact ((spfBasicOpen A f : Opens (spfSpace A)) : Set (spfSpace A)) :=
  isCompact_spfBasicOpen_of_isWeaklyPreAdmissible (A := A)
    (hA := isWeaklyPreAdmissible_of_isPreAdmissible hA) (f := f)

/-! ### The sections of the terms of the inverse system -/

/-- The sections of `𝒪_λ` over `D(f) ∩ Spf A` form an algebra over `A/I_λ`, being the sections of
the structure sheaf of `Spec (A/I_λ)` over the basic open of the image of `f`. -/
noncomputable instance algebra_spfComponentOn_spfBasicOpen (f : A) (I : SpfIndex A P) :
    Algebra (A ⧸ I.1) ((spfComponentOn A I).obj (op (spfBasicOpen A f))) :=
  StructureSheaf.openAlgebra _ _

/-- The sections of `𝒪_λ` over `D(f) ∩ Spf A` form an algebra over `A/I_λ`, being the sections of
the structure sheaf of `Spec (A/I_λ)` over the basic open of the image of `f`.

The ideals-of-definition case of `algebra_spfComponentOn_spfBasicOpen`. -/
noncomputable instance algebra_spfComponent_spfBasicOpen (f : A) (I : IdealsOfDefinition A) :
    Algebra (A ⧸ I.1) ((spfComponent A I).obj (op (spfBasicOpen A f))) :=
  algebra_spfComponentOn_spfBasicOpen (A := A) (P := IsIdealOfDefinition) (f := f) (I := I)

/-- The sections of `𝒪_λ` over `D(f) ∩ Spf A` are the localization `(A/I_λ)_f` of `A/I_λ` away
from the image of `f`, because `D(f) ∩ Spf A` pulls back to a basic open of `Spec (A/I_λ)`. -/
instance isLocalization_spfComponentOn_spfBasicOpen (f : A) (I : SpfIndex A P) :
    IsLocalization.Away (Ideal.Quotient.mk I.1 f)
      ((spfComponentOn A I).obj (op (spfBasicOpen A f))) :=
  StructureSheaf.IsLocalization.to_basicOpen _ _

/-- The sections of `𝒪_λ` over `D(f) ∩ Spf A` are the localization `(A/I_λ)_f` of `A/I_λ` away
from the image of `f`, because `D(f) ∩ Spf A` pulls back to a basic open of `Spec (A/I_λ)`.

The ideals-of-definition case of `isLocalization_spfComponentOn_spfBasicOpen`. -/
instance isLocalization_spfComponent_spfBasicOpen (f : A) (I : IdealsOfDefinition A) :
    IsLocalization.Away (Ideal.Quotient.mk I.1 f)
      ((spfComponent A I).obj (op (spfBasicOpen A f))) :=
  isLocalization_spfComponentOn_spfBasicOpen (A := A) (P := IsIdealOfDefinition) (f := f) (I := I)

omit [TopologicalSpace A] [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The powers of the image of `f` in `A/I` land in the powers of its image in `A/J`, for ideals
of definition `I ⊆ J`. -/
theorem spfAwayMapOn_le (f : A) {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    Submonoid.powers (Ideal.Quotient.mk I.1 f) ≤
      Submonoid.comap (Ideal.Quotient.factor h)
        (Submonoid.powers (Ideal.Quotient.mk J.1 f)) := by
  refine Submonoid.powers_le.2 ?_
  rw [Submonoid.mem_comap, Ideal.Quotient.factor_mk]
  exact Submonoid.mem_powers _

omit [IsTopologicalRing A] in
/-- The powers of the image of `f` in `A/I` land in the powers of its image in `A/J`, for ideals
of definition `I ⊆ J`.

The ideals-of-definition case of `spfAwayMapOn_le`. -/
theorem spfAwayMap_le (f : A) {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    Submonoid.powers (Ideal.Quotient.mk I.1 f) ≤
      Submonoid.comap (Ideal.Quotient.factor h)
        (Submonoid.powers (Ideal.Quotient.mk J.1 f)) :=
  spfAwayMapOn_le (A := A) (P := IsIdealOfDefinition) (f := f) (I := I) (J := J) (h := h)

omit [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The transition map `(A/I)_f → (A/J)_f` of the inverse system defining `A_{\{f\}}`, for ideals
of definition `I ⊆ J`: the localization of the surjection `A/I → A/J`. -/
noncomputable def spfAwayMapOn (f : A) {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    Localization.Away (Ideal.Quotient.mk I.1 f) →+* Localization.Away (Ideal.Quotient.mk J.1 f) :=
  IsLocalization.map _ (Ideal.Quotient.factor h) (spfAwayMapOn_le A f h)

/-- The transition map `(A/I)_f → (A/J)_f` of the inverse system defining `A_{\{f\}}`, for ideals
of definition `I ⊆ J`: the localization of the surjection `A/I → A/J`.

The ideals-of-definition case of `spfAwayMapOn`. -/
@[reducible] noncomputable def spfAwayMap (f : A) {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    Localization.Away (Ideal.Quotient.mk I.1 f) →+* Localization.Away (Ideal.Quotient.mk J.1 f) :=
  spfAwayMapOn (A := A) (P := IsIdealOfDefinition) (f := f) (I := I) (J := J) (h := h)

omit [TopologicalSpace A] [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The transition map of the inverse system of localizations is compatible with the maps from
the quotients: `(A/I)_f ← A/I → A/J → (A/J)_f` is `A/I → A/J → (A/J)_f`. -/
theorem spfAwayMapOn_comp_algebraMap (f : A) {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    (spfAwayMapOn A f h).comp (algebraMap (A ⧸ I.1) (Localization.Away (Ideal.Quotient.mk I.1 f)))
      = (algebraMap (A ⧸ J.1) (Localization.Away (Ideal.Quotient.mk J.1 f))).comp
          (Ideal.Quotient.factor h) :=
  IsLocalization.map_comp _

omit [IsTopologicalRing A] in
/-- The transition map of the inverse system of localizations is compatible with the maps from
the quotients: `(A/I)_f ← A/I → A/J → (A/J)_f` is `A/I → A/J → (A/J)_f`.

The ideals-of-definition case of `spfAwayMapOn_comp_algebraMap`. -/
theorem spfAwayMap_comp_algebraMap (f : A) {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    (spfAwayMap A f h).comp (algebraMap (A ⧸ I.1) (Localization.Away (Ideal.Quotient.mk I.1 f)))
      = (algebraMap (A ⧸ J.1) (Localization.Away (Ideal.Quotient.mk J.1 f))).comp
          (Ideal.Quotient.factor h) :=
  spfAwayMapOn_comp_algebraMap (A := A) (P := IsIdealOfDefinition) (f := f) (I := I) (J := J)
    (h := h)

omit [TopologicalSpace A] [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The transition map of the inverse system of localizations along `I ⊆ I` is the identity. -/
theorem spfAwayMapOn_self (f : A) (I : SpfIndex A P) :
    spfAwayMapOn A f (le_refl I.1) = RingHom.id _ :=
  IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk I.1 f)) (by
    rw [spfAwayMapOn_comp_algebraMap, RingHom.id_comp, Ideal.Quotient.factor_self, RingHom.comp_id])

omit [IsTopologicalRing A] in
/-- The transition map of the inverse system of localizations along `I ⊆ I` is the identity.

The ideals-of-definition case of `spfAwayMapOn_self`. -/
theorem spfAwayMap_self (f : A) (I : IdealsOfDefinition A) :
    spfAwayMap A f (le_refl I.1) = RingHom.id _ :=
  spfAwayMapOn_self (A := A) (P := IsIdealOfDefinition) (f := f) (I := I)

omit [TopologicalSpace A] [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The transition maps of the inverse system of localizations compose. -/
theorem spfAwayMapOn_comp (f : A) {I J K : SpfIndex A P} (h : I.1 ≤ J.1) (h' : J.1 ≤ K.1) :
    (spfAwayMapOn A f h').comp (spfAwayMapOn A f h) = spfAwayMapOn A f (h.trans h') :=
  IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk I.1 f)) (by
    rw [RingHom.comp_assoc, spfAwayMapOn_comp_algebraMap, ← RingHom.comp_assoc,
      spfAwayMapOn_comp_algebraMap, RingHom.comp_assoc, Ideal.Quotient.factor_comp,
      spfAwayMapOn_comp_algebraMap])

omit [IsTopologicalRing A] in
/-- The transition maps of the inverse system of localizations compose.

The ideals-of-definition case of `spfAwayMapOn_comp`. -/
theorem spfAwayMap_comp (f : A) {I J K : IdealsOfDefinition A} (h : I.1 ≤ J.1) (h' : J.1 ≤ K.1) :
    (spfAwayMap A f h').comp (spfAwayMap A f h) = spfAwayMap A f (h.trans h') :=
  spfAwayMapOn_comp (A := A) (P := IsIdealOfDefinition) (f := f) (I := I) (J := J) (K := K) (h := h)
    (h' := h')

/-- On sections over `D(f) ∩ Spf A` the transition map of the inverse system defining `𝒪_{Spf A}`
is the localization of the surjection `A/I → A/J`. -/
theorem spfTransitionOn_app_spfBasicOpen (f : A) {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    ((spfTransitionOn A h).app (op (spfBasicOpen A f))).hom
      = IsLocalization.map (M := Submonoid.powers (Ideal.Quotient.mk I.1 f))
          (T := Submonoid.powers (Ideal.Quotient.mk J.1 f)) _ (Ideal.Quotient.factor h)
          (Submonoid.powers_le.2 (Submonoid.mem_powers _)) :=
  StructureSheaf.comap_basicOpen _ _

/-- On sections over `D(f) ∩ Spf A` the transition map of the inverse system defining `𝒪_{Spf A}`
is the localization of the surjection `A/I → A/J`.

The ideals-of-definition case of `spfTransitionOn_app_spfBasicOpen`. -/
theorem spfTransition_app_spfBasicOpen (f : A) {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    ((spfTransition A h).app (op (spfBasicOpen A f))).hom
      = IsLocalization.map (M := Submonoid.powers (Ideal.Quotient.mk I.1 f))
          (T := Submonoid.powers (Ideal.Quotient.mk J.1 f)) _ (Ideal.Quotient.factor h)
          (Submonoid.powers_le.2 (Submonoid.mem_powers _)) :=
  spfTransitionOn_app_spfBasicOpen (A := A) (P := IsIdealOfDefinition) (f := f) (I := I) (J := J)
    (h := h)

/-- The transition map of `𝒪_{Spf A}` on sections over `D(f) ∩ Spf A` is compatible with the maps
from the quotients by the ideals of definition. -/
theorem spfTransitionOn_app_spfBasicOpen_comp_algebraMap (f : A) {I J : SpfIndex A P}
    (h : I.1 ≤ J.1) :
    ((spfTransitionOn A h).app (op (spfBasicOpen A f))).hom.comp
        (algebraMap (A ⧸ I.1) ((spfComponentOn A I).obj (op (spfBasicOpen A f))))
      = (algebraMap (A ⧸ J.1) ((spfComponentOn A J).obj (op (spfBasicOpen A f)))).comp
          (Ideal.Quotient.factor h) := by
  rw [spfTransitionOn_app_spfBasicOpen]
  exact IsLocalization.map_comp _

/-- The transition map of `𝒪_{Spf A}` on sections over `D(f) ∩ Spf A` is compatible with the maps
from the quotients by the ideals of definition.

The ideals-of-definition case of `spfTransitionOn_app_spfBasicOpen_comp_algebraMap`. -/
theorem spfTransition_app_spfBasicOpen_comp_algebraMap (f : A) {I J : IdealsOfDefinition A}
    (h : I.1 ≤ J.1) :
    ((spfTransition A h).app (op (spfBasicOpen A f))).hom.comp
        (algebraMap (A ⧸ I.1) ((spfComponent A I).obj (op (spfBasicOpen A f))))
      = (algebraMap (A ⧸ J.1) ((spfComponent A J).obj (op (spfBasicOpen A f)))).comp
          (Ideal.Quotient.factor h) :=
  spfTransitionOn_app_spfBasicOpen_comp_algebraMap (A := A) (P := IsIdealOfDefinition) (f := f)
    (I := I) (J := J) (h := h)

/-- The identification of the sections of `𝒪_λ` over `D(f) ∩ Spf A` with the localization
`(A/I_λ)_f`, as an isomorphism of `A/I_λ`-algebras. -/
noncomputable def spfAwayEquivOn (f : A) (I : SpfIndex A P) :
    ((spfComponentOn A I).obj (op (spfBasicOpen A f))) ≃ₐ[A ⧸ I.1]
      Localization.Away (Ideal.Quotient.mk I.1 f) :=
  IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk I.1 f)) _ _

/-- The identification of the sections of `𝒪_λ` over `D(f) ∩ Spf A` with the localization
`(A/I_λ)_f`, as an isomorphism of `A/I_λ`-algebras.

The ideals-of-definition case of `spfAwayEquivOn`. -/
@[reducible] noncomputable def spfAwayEquiv (f : A) (I : IdealsOfDefinition A) :
    ((spfComponent A I).obj (op (spfBasicOpen A f))) ≃ₐ[A ⧸ I.1]
      Localization.Away (Ideal.Quotient.mk I.1 f) :=
  spfAwayEquivOn (A := A) (P := IsIdealOfDefinition) (f := f) (I := I)

/-- The identifications of the sections of the `𝒪_λ` over `D(f) ∩ Spf A` with the localizations
`(A/I_λ)_f` are compatible with the transition maps of the two inverse systems. -/
theorem spfAwayEquivOn_naturality (f : A) {I J : SpfIndex A P} (h : I.1 ≤ J.1) :
    (spfAwayMapOn A f h).comp (spfAwayEquivOn A f I).toRingEquiv.toRingHom
      = (spfAwayEquivOn A f J).toRingEquiv.toRingHom.comp
          ((spfTransitionOn A h).app (op (spfBasicOpen A f))).hom :=
  have key (K : SpfIndex A P) :
      (spfAwayEquivOn A f K).toRingEquiv.toRingHom.comp
          (algebraMap (A ⧸ K.1) ((spfComponentOn A K).obj (op (spfBasicOpen A f))))
        = algebraMap (A ⧸ K.1) (Localization.Away (Ideal.Quotient.mk K.1 f)) :=
    (spfAwayEquivOn A f K).toAlgHom.comp_algebraMap
  IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk I.1 f)) (by
    rw [RingHom.comp_assoc, RingHom.comp_assoc, key I,
      spfTransitionOn_app_spfBasicOpen_comp_algebraMap, ← RingHom.comp_assoc, key J,
      spfAwayMapOn_comp_algebraMap])

/-- The identifications of the sections of the `𝒪_λ` over `D(f) ∩ Spf A` with the localizations
`(A/I_λ)_f` are compatible with the transition maps of the two inverse systems.

The ideals-of-definition case of `spfAwayEquivOn_naturality`. -/
theorem spfAwayEquiv_naturality (f : A) {I J : IdealsOfDefinition A} (h : I.1 ≤ J.1) :
    (spfAwayMap A f h).comp (spfAwayEquiv A f I).toRingEquiv.toRingHom
      = (spfAwayEquiv A f J).toRingEquiv.toRingHom.comp
          ((spfTransition A h).app (op (spfBasicOpen A f))).hom :=
  spfAwayEquivOn_naturality (A := A) (P := IsIdealOfDefinition) (f := f) (I := I) (J := J) (h := h)

/-! ### The inverse system `λ ↦ (A/I_λ)_f` and its limit -/

omit [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The localization `(A/I)_f` of a quotient by an ideal of definition, as a discrete topological
ring: the terms of the inverse system whose limit is the source's ring `A_{\{f\}}`. -/
def spfAwayObjOn (f : A) (I : SpfIndex A P) : TopCommRingCat.{u} :=
  letI : TopologicalSpace (Localization.Away (Ideal.Quotient.mk I.1 f)) := ⊥
  letI : DiscreteTopology (Localization.Away (Ideal.Quotient.mk I.1 f)) :=
    discreteTopology_bot _
  TopCommRingCat.of (Localization.Away (Ideal.Quotient.mk I.1 f))

/-- The localization `(A/I)_f` of a quotient by an ideal of definition, as a discrete topological
ring: the terms of the inverse system whose limit is the source's ring `A_{\{f\}}`.

The ideals-of-definition case of `spfAwayObjOn`. -/
@[reducible] def spfAwayObj (f : A) (I : IdealsOfDefinition A) : TopCommRingCat.{u} :=
  spfAwayObjOn (A := A) (P := IsIdealOfDefinition) (f := f) (I := I)

omit [IsTopologicalRing A] [IsWeakIdealSystem A P] in
/-- The topology on `(A/I)_f` as a term of the inverse system defining `A_{\{f\}}` is
discrete. -/
instance discreteTopology_spfAwayObjOn (f : A) (I : SpfIndex A P) :
    DiscreteTopology (spfAwayObjOn A f I).α :=
  discreteTopology_bot _

/-- The topology on `(A/I)_f` as a term of the inverse system defining `A_{\{f\}}` is
discrete.

The ideals-of-definition case of `discreteTopology_spfAwayObjOn`. -/
instance discreteTopology_spfAwayObj (f : A) (I : IdealsOfDefinition A) :
    DiscreteTopology (spfAwayObj A f I).α :=
  discreteTopology_spfAwayObjOn (A := A) (P := IsIdealOfDefinition) (f := f) (I := I)

omit [IsTopologicalRing A] [IsWeakIdealSystem A P] in
variable (P) in
/-- The inverse system `λ ↦ (A/I_λ)_f` of discrete topological rings whose limit is the source's
ring `A_{\{f\}}`, with transition maps the localizations of the surjections `A/I_λ → A/I_μ`. -/
noncomputable def spfAwayDiagramOn (f : A) : SpfIndex A P ⥤ TopCommRingCat.{u} where
  obj I := spfAwayObjOn A f I
  map h := ⟨spfAwayMapOn A f (leOfHom h), continuous_of_discreteTopology⟩
  map_id I := Subtype.ext (spfAwayMapOn_self A f I)
  map_comp h h' := Subtype.ext (spfAwayMapOn_comp A f (leOfHom h) (leOfHom h')).symm

/-- The inverse system `λ ↦ (A/I_λ)_f` of discrete topological rings whose limit is the source's
ring `A_{\{f\}}`, with transition maps the localizations of the surjections `A/I_λ → A/I_μ`.

The ideals-of-definition case of `spfAwayDiagramOn`. -/
@[reducible] noncomputable def spfAwayDiagram (f : A) : IdealsOfDefinition A ⥤ TopCommRingCat.{u} :=
  spfAwayDiagramOn (A := A) (P := IsIdealOfDefinition) (f := f)

/-- The sections of `𝒪_λ` over the quasi-compact open `D(f) ∩ Spf A` are discrete, that being the
defining property of the pseudo-discrete topology. -/
theorem discreteTopology_spfComponentOn_spfBasicOpen (hA : IsWeaklyPreAdmissible A) (f : A)
    (I : SpfIndex A P) :
    DiscreteTopology ((pseudoDiscrete (spfComponentOn A I)).obj (op (spfBasicOpen A f))).α :=
  isPseudoDiscrete_pseudoDiscrete (spfComponentOn A I) (spfBasicOpen A f)
    (isCompact_spfBasicOpen_of_isWeaklyPreAdmissible A hA f)

/-- The sections of `𝒪_λ` over the quasi-compact open `D(f) ∩ Spf A` are discrete, that being the
defining property of the pseudo-discrete topology.

The ideals-of-definition case of `discreteTopology_spfComponentOn_spfBasicOpen`. -/
theorem discreteTopology_spfComponent_spfBasicOpen (hA : IsPreAdmissible A) (f : A)
    (I : IdealsOfDefinition A) :
    DiscreteTopology ((pseudoDiscrete (spfComponent A I)).obj (op (spfBasicOpen A f))).α :=
  discreteTopology_spfComponentOn_spfBasicOpen (A := A) (P := IsIdealOfDefinition)
    (hA := isWeaklyPreAdmissible_of_isPreAdmissible hA) (f := f) (I := I)

/-- The identification of the sections of `𝒪_λ` over `D(f) ∩ Spf A` with the discrete topological
ring `(A/I_λ)_f`: the underlying rings are identified by `AlgebraicGeometry.spfAwayEquivOn`, and
both topologies are discrete. -/
noncomputable def spfAwayComponentIsoOn (hA : IsWeaklyPreAdmissible A) (f : A)
    (I : SpfIndex A P) :
    (pseudoDiscrete (spfComponentOn A I)).obj (op (spfBasicOpen A f)) ≅ spfAwayObjOn A f I :=
  letI := discreteTopology_spfComponentOn_spfBasicOpen A hA f I
  { hom := ⟨(spfAwayEquivOn A f I).toRingEquiv.toRingHom, continuous_of_discreteTopology⟩
    inv := ⟨(spfAwayEquivOn A f I).symm.toRingEquiv.toRingHom, continuous_of_discreteTopology⟩
    hom_inv_id := Subtype.ext (RingHom.ext fun s => (spfAwayEquivOn A f I).symm_apply_apply s)
    inv_hom_id := Subtype.ext (RingHom.ext fun s => (spfAwayEquivOn A f I).apply_symm_apply s) }

/-- The identification of the sections of `𝒪_λ` over `D(f) ∩ Spf A` with the discrete topological
ring `(A/I_λ)_f`: the underlying rings are identified by `AlgebraicGeometry.spfAwayEquiv`, and
both topologies are discrete.

The ideals-of-definition case of `spfAwayComponentIsoOn`. -/
@[reducible] noncomputable def spfAwayComponentIso (hA : IsPreAdmissible A) (f : A)
    (I : IdealsOfDefinition A) :
    (pseudoDiscrete (spfComponent A I)).obj (op (spfBasicOpen A f)) ≅ spfAwayObj A f I :=
  spfAwayComponentIsoOn (A := A) (P := IsIdealOfDefinition)
    (hA := isWeaklyPreAdmissible_of_isPreAdmissible hA) (f := f) (I := I)

variable (P) in
/-- The inverse system of the sections over `D(f) ∩ Spf A` of the terms of `𝒪_{Spf A}` is the
inverse system `λ ↦ (A/I_λ)_f` of discrete topological rings. -/
noncomputable def spfAwayDiagramIsoOn (hA : IsWeaklyPreAdmissible A) (f : A) :
    (spfDiagramOn A P ⋙ pseudoDiscreteFunctor) ⋙
        (evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op (spfBasicOpen A f))
      ≅ spfAwayDiagramOn A P f :=
  NatIso.ofComponents (fun I => spfAwayComponentIsoOn A hA f I)
    fun h => Subtype.ext (spfAwayEquivOn_naturality A f (leOfHom h)).symm

/-- The inverse system of the sections over `D(f) ∩ Spf A` of the terms of `𝒪_{Spf A}` is the
inverse system `λ ↦ (A/I_λ)_f` of discrete topological rings.

The ideals-of-definition case of `spfAwayDiagramIsoOn`. -/
@[reducible] noncomputable def spfAwayDiagramIso (hA : IsPreAdmissible A) (f : A) :
    (spfDiagram A ⋙ pseudoDiscreteFunctor) ⋙
        (evaluation ((Opens (spfSpace A))ᵒᵖ) TopCommRingCat.{u}).obj (op (spfBasicOpen A f))
      ≅ spfAwayDiagram A f :=
  spfAwayDiagramIsoOn (A := A) (P := IsIdealOfDefinition)
    (hA := isWeaklyPreAdmissible_of_isPreAdmissible hA) (f := f)

variable (P) in
/-- **Deferred by the source** ("At this point one should check several things"):
`Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}} = lim_λ (A/I_λ)_f` as topological rings. The sections of
`𝒪_{Spf A} = lim_λ 𝒪_λ` over an open are the limit of the sections of the `𝒪_λ` there, and over
the quasi-compact open `D(f) ∩ Spf A` those sections are the discrete rings `(A/I_λ)_f`. -/
noncomputable def spfBasicOpenIsoOn (hA : IsWeaklyPreAdmissible A) (f : A) :
    (spfPresheafOn A P).obj (op (spfBasicOpen A f)) ≅ limit (spfAwayDiagramOn A P f) :=
  limitObjIsoLimitCompEvaluation (spfDiagramOn A P ⋙ pseudoDiscreteFunctor)
      (op (spfBasicOpen A f))
    ≪≫ HasLimit.isoOfNatIso (spfAwayDiagramIsoOn A P hA f)

/-- **Deferred by the source** ("At this point one should check several things"):
`Γ(D(f) ∩ Spf A, 𝒪_{Spf A}) = A_{\{f\}} = lim_λ (A/I_λ)_f` as topological rings. The sections of
`𝒪_{Spf A} = lim_λ 𝒪_λ` over an open are the limit of the sections of the `𝒪_λ` there, and over
the quasi-compact open `D(f) ∩ Spf A` those sections are the discrete rings `(A/I_λ)_f`.

The ideals-of-definition case of `spfBasicOpenIsoOn`. -/
@[reducible] noncomputable def spfBasicOpenIso (hA : IsPreAdmissible A) (f : A) :
    (spfPresheaf A).obj (op (spfBasicOpen A f)) ≅ limit (spfAwayDiagram A f) :=
  spfBasicOpenIsoOn (A := A) (P := IsIdealOfDefinition)
    (hA := isWeaklyPreAdmissible_of_isPreAdmissible hA) (f := f)

end AlgebraicGeometry
