module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.NormalizationAlmostIso
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingProducer
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.DimensionOne
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotient.StalkVanishing
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# The normalization of a reduced curve is an isomorphism away from finitely many points

This file supplies the last clause of `Stacks.GlueSquishFactor.IsAlmostIso` for the
normalization `ν : X^ν ⟶ X` of a reduced scheme locally of finite type over a field and of
dimension at most one, namely

**`∃ U, Set.Finite ((U : Set X)ᶜ) ∧ IsIso (ν ∣_ U)`**,

and hence `Stacks.GlueSquishFactor.IsAlmostIso ν` outright, by feeding it to
`AlgebraicGeometry.isAlmostIso_normalizationOverField_of_exists_isIso`, which discharges the
other six clauses.

The open set is the regular locus. Three facts combine. First, the stalk of
`ν^♯ : 𝒪_X ⟶ ν_*𝒪_{X^ν}` at a point `x` is the inclusion of `𝒪_{X,x}` into its integral closure
in its own total ring of fractions ([Stacks, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
(2)), so it is injective always, and surjective exactly when `𝒪_{X,x}` is integrally closed —
which holds at a regular point. Second, a morphism of sheaves whose stalk maps are isomorphisms
at every point of an open `V` is an isomorphism on sections over `V`; combined with the first
point and the affineness of `ν` this makes `ν` an isomorphism over every affine open inside the
regular locus, hence, `IsIso` being Zariski-local on the target, over the whole regular locus.
Third, in dimension at most one the regular locus of a reduced Nagata scheme is open with
finite complement.

## Implementation notes

**Why the regular locus and not the normal locus.** The criterion
`AlgebraicGeometry.isIso_of_isIntegralHom_of_isBirational_of_isNormal` ([Stacks, Tag 0AB1]) asks
for an *integral* source and target, which an open of a reducible curve is not, and the normal
locus of a reduced scheme is not available as an open set: openness of the normal locus is
carried only in the ring-theoretic form
`PrimeSpectrum.isOpen_setOf_isIntegrallyClosed_atPrime` ([Stacks, Tag 0332]), for a *domain*
and under an extra hypothesis. Neither obstacle is real, because the whole question is local on
the target and the point-local statement already exists: the normalization stalk map is
described by Tag 0C3B(2), and at a regular point the local ring is integrally closed by
`isIntegrallyClosed_of_isRegularLocalRing`. The regular locus is open with discrete complement
for a reduced one-dimensional Nagata scheme, by
`AlgebraicGeometry.isOpen_regularLocus_of_isNagataScheme` and
`AlgebraicGeometry.not_subset_singularLocus_of_mem_irreducibleComponents`. In dimension at most
one the two loci in fact agree — that is
`Stacks.AlgebraicGeometry.NormalizationQuotient.isZero_normalizationQuotientStalk_iff_regular` —
so nothing is lost.

**Globality of the finiteness.** `finite_singularLocus_inter_of_isAffineOpen` bounds the
singular locus on one affine open. The global statement needs quasi-compactness, which is what
`QuasiCompact p` gives over the compact base `Spec k`: `X` is then a Noetherian space and the
singular locus is a closed subset of it containing no irreducible component, hence finite by
`Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset`.

**The dimension hypothesis.** It is `topologicalKrullDim X ≤ 1` rather than `= 1`, which is
what the proof uses, and it is not an added hypothesis in disguise: the conclusion is false
without it, the non-normal locus of a reduced surface being a curve.

## Main results

* `AlgebraicGeometry.isIso_stalkFunctor_map_normalization` — the stalk of `ν^♯` at a regular
  point is an isomorphism.
* `AlgebraicGeometry.isIso_app_normalization_of_subset_regularLocus` — `ν^♯` is an isomorphism
  on sections over any open inside the regular locus.
* `AlgebraicGeometry.isIso_morphismRestrict_normalization_of_subset_regularLocus` — `ν` is an
  isomorphism over any open inside the regular locus.
* `AlgebraicGeometry.finite_singularLocus_of_compactSpace` — the singular locus of a reduced
  quasi-compact Nagata scheme of dimension at most one is finite.
* `AlgebraicGeometry.exists_isIso_morphismRestrict_normalizationOverField` — the clause itself.
* `AlgebraicGeometry.isAlmostIso_normalizationOverField` — `IsAlmostIso ν`, with no hypothesis
  left over.
* `AlgebraicGeometry.isElementaryChain_normalizationOverField` — hence [Stacks, Tag 0C1L] for
  the normalization: `ν` is a chain of glueings of two rational points and squishings of tangent
  vectors.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C1R](https://stacks.math.columbia.edu/tag/0C1R)
* [Stacks Project, Tag 0C3B](https://stacks.math.columbia.edu/tag/0C3B)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- **An affine morphism that is an isomorphism on sections over every affine open inside `U` is
an isomorphism over `U`.** Being an isomorphism is Zariski-local on the target, and over an
affine open an affine morphism is an isomorphism exactly when it is one on sections. -/
theorem isIso_morphismRestrict_of_forall_isAffineOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] (U : Y.Opens)
    (h : ∀ V : Y.Opens, IsAffineOpen V → V ≤ U → IsIso (f.app V)) :
    IsIso (f ∣_ U) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms Scheme) fun y ↦ ?_
  obtain ⟨-, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    U.toScheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  refine ⟨W, hyW, ?_⟩
  rw [MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictRestrict f U W), MorphismProperty.isomorphisms.iff]
  exact (isIso_morphismRestrict_iff_isIso_app f (hW.image_of_isOpenImmersion U.ι)).mpr
    (h _ (hW.image_of_isOpenImmersion U.ι) (U.ι_image_le W))

variable {X : Scheme.{u}}

open Stacks.AlgebraicGeometry.NormalizationQuotient in
/-- **At a regular point the stalk of `𝒪_X ⟶ ν_*𝒪_{X^ν}` is an isomorphism.** By [Stacks, Tag
0C3B](https://stacks.math.columbia.edu/tag/0C3B)(2) that stalk map is the inclusion of
`𝒪_{X,x}` into its integral closure in its own total ring of fractions, which is injective
always and surjective precisely when `𝒪_{X,x}` is integrally closed — as a regular local ring
is. -/
theorem isIso_stalkFunctor_map_normalization [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {x : X} (hx : x ∈ regularLocus X) :
    IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (Scheme.normalization X hX).c) := by
  have _ : IsRegularLocalRing (X.presheaf.stalk x) := hx
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨normalizationPushforwardStalk_map_injective X hX x,
    normalizationStalkMap_surjective_of_isIntegrallyClosed X hX x
      (isIntegrallyClosed_of_isRegularLocalRing _)⟩

/-- **The normalization morphism is an isomorphism on sections over any open contained in the
regular locus.** A morphism of sheaves whose stalk maps are isomorphisms at every point of an
open is an isomorphism on sections over it. -/
theorem isIso_app_normalization_of_subset_regularLocus [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (V : X.Opens) (hV : (V : Set X) ⊆ regularLocus X) :
    IsIso ((Scheme.normalization X hX).app V) := by
  let φ : X.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat (Scheme.normalization X hX).base).obj
        (Scheme.normalizationScheme X hX).sheaf := ⟨(Scheme.normalization X hX).c⟩
  have _ : ∀ x : V, IsIso ((TopCat.Presheaf.stalkFunctor CommRingCat x.1).map φ.1) :=
    fun x ↦ isIso_stalkFunctor_map_normalization hX (hV x.2)
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso φ V

/-- **The normalization morphism is an isomorphism over any open contained in the regular
locus.** -/
theorem isIso_morphismRestrict_normalization_of_subset_regularLocus [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (U : X.Opens) (hU : (U : Set X) ⊆ regularLocus X) :
    IsIso (Scheme.normalization X hX ∣_ U) :=
  isIso_morphismRestrict_of_forall_isAffineOpen _ U fun V _ hVU ↦
    isIso_app_normalization_of_subset_regularLocus hX V
      ((show (V : Set X) ⊆ (U : Set X) from hVU).trans hU)

/-- **The singular locus of a reduced quasi-compact Nagata scheme of dimension at most one is
finite.** It is a closed subset of a Noetherian sober space of dimension at most one containing
no irreducible component, since the generic point of a component of a reduced scheme is
regular. -/
theorem finite_singularLocus_of_compactSpace (X : Scheme.{u}) [IsReduced X] [CompactSpace X]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X ≤ 1) :
    (singularLocus X).Finite := by
  have _ : IsLocallyNoetherian X :=
    ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme X).mp hNagata).1
  have _ : IsNoetherian X := IsNoetherian.mk
  exact Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim
    (isOpen_regularLocus_of_isNagataScheme X hNagata hdim).isClosed_compl
    fun _ hC ↦ not_subset_singularLocus_of_mem_irreducibleComponents X hC

/-- **The normalization of a reduced scheme locally of finite type and quasi-compact over a
field, of dimension at most one, is an isomorphism over an open set with finite complement.**

This is the one clause of `Stacks.GlueSquishFactor.IsAlmostIso` that
`AlgebraicGeometry.isAlmostIso_normalizationOverField_of_exists_isIso` leaves open. The open
set is the regular locus. -/
theorem exists_isIso_morphismRestrict_normalizationOverField (k : Type u) [Field k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ U : X.Opens, Set.Finite ((U : Set X)ᶜ) ∧ IsIso (normalizationOverField k p ∣_ U) := by
  have hNagata : IsNagataScheme X := isNagataScheme_of_locallyOfFiniteType_over_field k p
  have _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨⟨regularLocus X, isOpen_regularLocus_of_isNagataScheme X hNagata hdim⟩,
    finite_singularLocus_of_compactSpace X hNagata hdim,
    isIso_morphismRestrict_normalization_of_subset_regularLocus _ _ le_rfl⟩

/-- **The normalization of a reduced algebraic scheme of dimension at most one over an
algebraically closed field is an almost isomorphism in the sense of [Stacks, Tag
0C1L](https://stacks.math.columbia.edu/tag/0C1L).**

All seven clauses of `Stacks.GlueSquishFactor.IsAlmostIso` are now discharged: six by
`AlgebraicGeometry.isAlmostIso_normalizationOverField_of_exists_isIso`, and the seventh by
`AlgebraicGeometry.exists_isIso_morphismRestrict_normalizationOverField`. Composed with
`Stacks.GlueSquishFactor.IsAlmostIso.isElementaryChain` this factors `ν` as an elementary
chain. -/
theorem isAlmostIso_normalizationOverField (k : Type u) [Field k] [IsAlgClosed k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) :
    Stacks.GlueSquishFactor.IsAlmostIso
      (Over.homMk (normalizationOverField k p) rfl :
        Over.mk (normalizationOverField k p ≫ p) ⟶ Over.mk p) :=
  isAlmostIso_normalizationOverField_of_exists_isIso k p
    (exists_isIso_morphismRestrict_normalizationOverField k p hdim)

/-- **The normalization of a reduced algebraic scheme of dimension at most one over an
algebraically closed field is a chain of glueings of two rational points and squishings of
tangent vectors.** This is [Stacks, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L), in the
form `Stacks.GlueSquishFactor.IsAlmostIso.isElementaryChain` carries it, applied to the
normalization: the hypothesis `Stacks.GlueSquishFactor.IsAlmostIso` is now available for `ν`
with nothing left over. -/
theorem isElementaryChain_normalizationOverField (k : Type u) [Field k] [IsAlgClosed k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p] [IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) :
    Stacks.GlueSquishFactor.IsElementaryChain k
      (Over.homMk (normalizationOverField k p) rfl :
        Over.mk (normalizationOverField k p ≫ p) ⟶ Over.mk p) :=
  Stacks.GlueSquishFactor.IsAlmostIso.isElementaryChain _
    (isAlmostIso_normalizationOverField k p hdim)

end AlgebraicGeometry

end
