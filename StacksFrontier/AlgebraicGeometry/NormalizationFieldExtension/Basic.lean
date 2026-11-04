module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Functorial
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Normalization

/-!
# Normalization and extension of the ground field: the comparison through generic points

Let `X` be a scheme locally of finite type over a field `k`, and let `K/k` be an extension of
fields. Writing `X_K` for the base change of `X`, there is a canonical morphism from the
normalization of `X_K` to the base change of the normalization of `X`. That comparison morphism
is `AlgebraicGeometry.normalizationBaseChangeComparison`, and it, the base change
`AlgebraicGeometry.baseChangeNormalization` of the normalization morphism, and the
identification of the two projections out of the fibre product are in
`StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic`, which this file imports.

What is added here is the intermediate layer of that construction, in a form that does not
mention flatness. A morphism carrying generic points to generic points induces a morphism of
the coproducts of the spectra of the residue fields at the generic points (Tag 035M), and
functoriality of relative normalization (Tag 035J) turns that into a morphism of normalizations
(Tag 035N). Specialized to the projection `X_K ⟶ X` these give the two named components of the
comparison morphism, which the fibre-product projection formulas refer to.

## Main definitions

* `AlgebraicGeometry.Scheme.genericPointResidueSpectrumMap` is the morphism of generic-point
  residue spectra induced by a morphism carrying generic points to generic points. Unlike
  `AlgebraicGeometry.Scheme.Hom.genericPointResidueSpectrumMap` it takes the generic-point
  condition as an explicit hypothesis rather than deducing it from an instance of `Flat`, so it
  does not depend on how that condition was established.
* `AlgebraicGeometry.specMapAlgebraMap` is the morphism of affine spectra induced by an
  extension of the ground ring.
* `AlgebraicGeometry.genericPointResidueSpectrumBaseChangeMap` and
  `AlgebraicGeometry.normalizationBaseChangeMap` specialize the above to the projection
  `X_K ⟶ X`.

## Main results

* `AlgebraicGeometry.mem_genericPoints_of_generalizingMap_of_continuous`: a continuous
  generalizing map into a quasi-sober space carries generic points to generic points. This
  trades the sobriety and `T0` hypotheses on the source of
  `AlgebraicGeometry.mem_genericPoints_of_generalizingMap` for continuity of the map; neither
  statement implies the other.
* `AlgebraicGeometry.baseChangeNormalization_fst` and
  `AlgebraicGeometry.baseChangeNormalization_snd` compute the two projections of the base change
  of the normalization morphism.

## Implementation notes

Schemes over a field are objects of the over category and base change is `Over.pullback`, so
the base change of `X` along `K/k` is `pullback X.hom (Spec.map (CommRingCat.ofHom
(algebraMap k K)))`. Local finite type over a field supplies the finiteness of irreducible
components of quasi-compact opens that the normalization of Tag 035N requires; that is
`AlgebraicGeometry.finite_irreducibleComponents_of_locallyOfFiniteType`.

Several proofs below are written in term mode. The reason is that
`AlgebraicGeometry.Scheme.genericPointResidueSpectrum` is a semireducible definition wrapping a
coproduct, so a goal produced by `CategoryTheory.Limits.Sigma.hom_ext` is well typed only at
default transparency; `rw` and `simp` cannot operate on it, while term-level composition can.

No `@[stacks 0C3N]` attribute is attached in this file: the four assertions of the tag that are
formalized all sit on declarations in
`StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Basic`.

## References

* [Stacks Project, Tag 0C3N](https://stacks.math.columbia.edu/tag/0C3N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A continuous map that lifts generalizations into a quasi-sober space carries generic points
to generic points: a generization of the image of a generic point lifts to a generization of
that point, which maximality of its closure forces back into that closure.

This is the variant of `AlgebraicGeometry.mem_genericPoints_of_generalizingMap` that assumes the
map continuous instead of assuming the source sober and `T0`. -/
public theorem mem_genericPoints_of_generalizingMap_of_continuous {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [QuasiSober β] {f : α → β} (hcont : Continuous f)
    (hf : GeneralizingMap f) {x : α} (hx : x ∈ genericPoints α) :
    f x ∈ genericPoints β := by
  refine ⟨isIrreducible_singleton.closure, fun s hs hsub ↦ ?_⟩
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hs.closure isClosed_closure
  have hmem : f x ∈ closure {ξ} :=
    hξ.symm ▸ subset_closure (hsub (subset_closure (Set.mem_singleton _)))
  obtain ⟨x', hx', rfl⟩ := hf (specializes_iff_mem_closure.2 hmem)
  have h : f x' ∈ closure {f x} := by
    simpa using image_closure_subset_closure_image (s := ({x} : Set α)) hcont
      ⟨x', hx.2 isIrreducible_singleton.closure hx'.closure_subset
        (subset_closure (Set.mem_singleton _)), rfl⟩
  calc s ⊆ closure s := subset_closure
    _ = closure {f x'} := hξ.symm
    _ ⊆ closure {f x} := closure_minimal (Set.singleton_subset_iff.2 h) isClosed_closure

namespace Scheme

/-- The morphism of generic-point residue spectra induced by a morphism of schemes that carries
generic points to generic points: on the summand at a generic point it is the spectrum of the
residue-field map, landing in the summand at the image point. -/
public noncomputable def genericPointResidueSpectrumMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ x ∈ genericPoints X, f x ∈ genericPoints Y) :
    genericPointResidueSpectrum X ⟶ genericPointResidueSpectrum Y :=
  Sigma.desc fun η ↦ Spec.map (f.residueFieldMap η.1) ≫
    Sigma.ι (fun ξ : genericPoints Y ↦ Spec (.of (Y.residueField ξ.1))) ⟨f η.1, hf η.1 η.2⟩

/-- The induced morphism of generic-point residue spectra restricts on the summand at a generic
point to the spectrum of the residue-field map followed by the inclusion of the summand at the
image point. -/
@[reassoc]
public theorem ι_genericPointResidueSpectrumMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ x ∈ genericPoints X, f x ∈ genericPoints Y) (η : genericPoints X) :
    Sigma.ι (fun η : genericPoints X ↦ Spec (.of (X.residueField η.1))) η ≫
        genericPointResidueSpectrumMap f hf =
      Spec.map (f.residueFieldMap η.1) ≫
        Sigma.ι (fun ξ : genericPoints Y ↦ Spec (.of (Y.residueField ξ.1)))
          ⟨f η.1, hf η.1 η.2⟩ :=
  Sigma.ι_desc _ _

/-- The induced morphism of generic-point residue spectra lies over the given morphism. -/
@[reassoc]
public theorem genericPointResidueSpectrumMap_fromGenericPointResidueFields
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : ∀ x ∈ genericPoints X, f x ∈ genericPoints Y) :
    genericPointResidueSpectrumMap f hf ≫ fromGenericPointResidueFields Y =
      fromGenericPointResidueFields X ≫ f :=
  Sigma.hom_ext _ _ fun η ↦
    (ι_genericPointResidueSpectrumMap_assoc f hf η (fromGenericPointResidueFields Y)).trans <|
      (congrArg (fun g ↦ Spec.map (f.residueFieldMap η.1) ≫ g)
          (genericPointResidueSpectrum_ι_fromGenericPointResidueFields Y
            ⟨f η.1, hf η.1 η.2⟩)).trans <|
        (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f η.1).trans
          (genericPointResidueSpectrum_ι_fromGenericPointResidueFields_assoc X η f).symm

end Scheme

/-- The morphism of affine spectra induced by an extension of the ground ring. -/
public noncomputable abbrev specMapAlgebraMap (k K : Type u) [CommRing k] [CommRing K]
    [Algebra k K] : Spec (.of K) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k K))

section BaseChange

variable {k K : Type u} [Field k] [Field K] [Algebra k K] (X : Over (Spec (.of k)))

/-- The morphism from the generic-point residue spectrum of a scheme is quasi-separated. -/
local instance quasiSeparatedFromGenericPointResidueFields' (Z : Scheme.{u}) :
    QuasiSeparated (Scheme.fromGenericPointResidueFields Z) :=
  Scheme.quasiSeparatedFromGenericPointResidueFields Z

variable [LocallyOfFiniteType X.hom] in
/-- For a scheme locally of finite type over a field, the morphism from its generic-point residue
spectrum is quasi-compact. -/
local instance quasiCompactFromGenericPointResidueFields_left :
    QuasiCompact (Scheme.fromGenericPointResidueFields X.left) :=
  Scheme.quasiCompactFromGenericPointResidueFields X.left
    (finite_irreducibleComponents_of_locallyOfFiniteType k X.hom)

variable [LocallyOfFiniteType X.hom] in
/-- For a scheme locally of finite type over `k`, the morphism from the generic-point residue
spectrum of its base change to `K` is quasi-compact. -/
local instance quasiCompactFromGenericPointResidueFields_baseChange :
    QuasiCompact (Scheme.fromGenericPointResidueFields
      (pullback X.hom (specMapAlgebraMap k K))) :=
  Scheme.quasiCompactFromGenericPointResidueFields _
    (finite_irreducibleComponents_of_locallyOfFiniteType K
      (pullback.snd X.hom (specMapAlgebraMap k K)))

/-- The projection from the base change to the original scheme carries generic points to
generic points: it is a base change of `Spec K ⟶ Spec k`, hence flat, hence generizing. -/
public theorem mem_genericPoints_pullbackFst :
    ∀ x ∈ genericPoints ↥(pullback X.hom (specMapAlgebraMap k K)),
      pullback.fst X.hom (specMapAlgebraMap k K) x ∈ genericPoints X.left := by
  have := flat_specMap_algebraMap k K
  exact fun _ hx ↦ Scheme.Hom.mem_genericPoints_of_flat _ hx

/-- The morphism of generic-point residue spectra induced by extending the ground field. -/
public noncomputable def genericPointResidueSpectrumBaseChangeMap :
    Scheme.genericPointResidueSpectrum (pullback X.hom (specMapAlgebraMap k K)) ⟶
      Scheme.genericPointResidueSpectrum X.left :=
  Scheme.genericPointResidueSpectrumMap (pullback.fst X.hom (specMapAlgebraMap k K))
    (mem_genericPoints_pullbackFst X)

/-- The induced morphism of generic-point residue spectra lies over the projection to the
original scheme. -/
public theorem genericPointResidueSpectrumBaseChangeMap_comp :
    genericPointResidueSpectrumBaseChangeMap X ≫
        Scheme.fromGenericPointResidueFields X.left =
      Scheme.fromGenericPointResidueFields (pullback X.hom (specMapAlgebraMap k K)) ≫
        pullback.fst X.hom (specMapAlgebraMap k K) :=
  Scheme.genericPointResidueSpectrumMap_fromGenericPointResidueFields
    (pullback.fst X.hom (specMapAlgebraMap k K)) (mem_genericPoints_pullbackFst X)

variable [LocallyOfFiniteType X.hom]

/-- The morphism of normalizations induced by the base-change square, through functoriality of
relative normalization. -/
public noncomputable abbrev normalizationBaseChangeMap :
    normalizationSchemeOverField K (pullback.snd X.hom (specMapAlgebraMap k K)) ⟶
      normalizationSchemeOverField k X.hom :=
  Scheme.Hom.normalizationMap (Scheme.fromGenericPointResidueFields X.left)
    (Scheme.fromGenericPointResidueFields (pullback X.hom (specMapAlgebraMap k K)))
    (genericPointResidueSpectrumBaseChangeMap X)
    (pullback.fst X.hom (specMapAlgebraMap k K))
    (genericPointResidueSpectrumBaseChangeMap_comp X)

/-- The induced morphism of normalizations lies over the projection to the original scheme. -/
@[reassoc]
public theorem normalizationBaseChangeMap_comp :
    normalizationBaseChangeMap X ≫ normalizationOverField k X.hom =
      normalizationOverField K (pullback.snd X.hom (specMapAlgebraMap k K)) ≫
        pullback.fst X.hom (specMapAlgebraMap k K) :=
  Scheme.Hom.normalizationMap_fromNormalization _ _ _ _ _

/-- The base change of the normalization morphism projects to the normalization morphism. -/
@[reassoc]
public theorem baseChangeNormalization_fst :
    baseChangeNormalization X ≫ pullback.fst X.hom (specMapAlgebraMap k K) =
      pullback.fst (normalizationOverField k X.hom ≫ X.hom) (specMapAlgebraMap k K) ≫
        normalizationOverField k X.hom := by
  simp only [baseChangeNormalization]
  exact pullback.lift_fst _ _ _

/-- The base change of the normalization morphism commutes with the projections to `Spec K`. -/
@[reassoc]
public theorem baseChangeNormalization_snd :
    baseChangeNormalization X ≫ pullback.snd X.hom (specMapAlgebraMap k K) =
      pullback.snd (normalizationOverField k X.hom ≫ X.hom) (specMapAlgebraMap k K) := by
  simp only [baseChangeNormalization]
  exact pullback.lift_snd _ _ _

end BaseChange

end AlgebraicGeometry
