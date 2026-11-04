module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Reduction
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.UniversalProperty
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Normalization
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic

/-!
# Normalization of a scheme locally of finite type over a field

Let `k` be a field and let `X` be locally of finite type over `k`. The normalization morphism
`ν : X^ν → X` is finite and dominant, `X^ν` is a disjoint union of normal irreducible schemes
each again locally of finite type over `k`, and `ν` factors through the reduction of `X` as the
normalization of that reduction. If `X` is reduced then `ν` is birational, and if `X` is a
variety then so is `X^ν`. Properness of `X` over `k` passes to `X^ν`, and the relative
normalization of `X` in a reduced scheme locally of finite type over `k` is finite.

## Main results

* `AlgebraicGeometry.exists_iso_normalizationSchemeOverField_coproduct_normal_irreducible`
  decomposes the normalization into normal irreducible pieces locally of finite type over `k`.
* `AlgebraicGeometry.isVariety_normalizationOverField`: the normalization of a variety is a
  variety.
* `AlgebraicGeometry.isProper_normalizationOverField_comp`: the normalization of a proper scheme
  over `k` is proper over `k`. This is the properness half of [Stacks, Tag 0GK4]; the tag is
  carried by `AlgebraicGeometry.isProper_and_isProjective_normalizationOverField`, which also has
  the projectivity assertion.
* `AlgebraicGeometry.isFinite_fromNormalization_of_locallyOfFiniteType_over_field`: the
  relative normalization of `X` in a reduced `Y`, both locally of finite type over `k`, is
  finite.

## Implementation notes

A locally algebraic `k`-scheme is represented by its structure morphism to `Spec k` together
with a `LocallyOfFiniteType` instance; `AlgebraicGeometry.normalizationOverField` is the
normalization morphism formed from the resulting finiteness of irreducible components. A disjoint
union is a coproduct together with an isomorphism, and each summand carries the structure
morphism induced by its coproduct inclusion.

Finiteness and dominance of the normalization morphism, its birationality over a reduced scheme,
and its factorization through the reduction are already available over weaker hypotheses as
`AlgebraicGeometry.isFinite_normalizationOverField`,
`AlgebraicGeometry.isDominant_normalizationOverField`,
`AlgebraicGeometry.Scheme.isBirational_normalization` and
`AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_reduction`; the corresponding
assertions of the source are recorded against those declarations rather than restated here. The
source states finiteness and birationality twice, once in general and once for a variety; after
this identification both readings are carried by the same two declarations.

## References

* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
* [Stacks Project, Tag 0BXS](https://stacks.math.columbia.edu/tag/0BXS)
* [Stacks Project, Tag 0GK4](https://stacks.math.columbia.edu/tag/0GK4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

add_to_stacks 0BXR "finite_normal_components" AlgebraicGeometry.isFinite_normalizationOverField
add_to_stacks 0BXR "finite_normal_components" AlgebraicGeometry.isDominant_normalizationOverField
add_to_stacks 0BXR "birational_reduced" AlgebraicGeometry.Scheme.isBirational_normalization
add_to_stacks 0BXR "normalization_of_reduction"
  AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_reduction

/-- **Stacks Project, Tag 0BXR.** The normalization of a scheme locally of finite type over a
field is a coproduct of normal irreducible schemes, each locally of finite type over the field
via its induced structure morphism. -/
@[stacks 0BXR "finite_normal_components"]
public theorem exists_iso_normalizationSchemeOverField_coproduct_normal_irreducible
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    ∃ (I : Type u) (Z : I → Scheme.{u})
      (_ : ∀ i, IrreducibleSpace (Z i)) (_ : ∀ i, IsNormal (Z i))
      (e : normalizationSchemeOverField k p ≅ ∐ Z),
      ∀ i, LocallyOfFiniteType (Sigma.ι Z i ≫ e.inv ≫ normalizationOverField k p ≫ p) := by
  let : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  have hnorm : IsNormal (normalizationSchemeOverField k p) :=
    Scheme.isNormal_normalizationScheme X
      (finite_irreducibleComponents_of_locallyOfFiniteType k p)
  have hfin : ∀ U : (normalizationSchemeOverField k p).Opens,
      IsCompact (U : Set (normalizationSchemeOverField k p)) →
      (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_locallyOfFiniteType k (normalizationOverField k p ≫ p)
  obtain ⟨I, Z, hNormal, hIntegral, ⟨e⟩⟩ := (isNormal_iff_exists_iso_coproduct hfin).mp hnorm
  exact ⟨I, Z, fun i ↦ have := hIntegral i; inferInstance, hNormal, e, fun _ ↦ inferInstance⟩

/-- **Stacks Project, Tag 0BXR.** The normalization of a variety is a variety over the same
field. -/
@[stacks 0BXR "normalization_of_variety"]
public instance isVariety_normalizationOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsVariety k p] :
    IsVariety k (normalizationOverField k p ≫ p) := by
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  have hbir : IsBirational (normalizationOverField k p) :=
    Scheme.isBirational_normalization X hX
  let : IsFinite (normalizationOverField k p) := isFinite_normalizationOverField k p
  let : IsReduced (normalizationSchemeOverField k p) := Scheme.isReduced_normalizationScheme X hX
  let : IrreducibleSpace X :=
    ((isIntegral_iff_irreducibleSpace_and_isReduced X).mp inferInstance).1
  have : IrreducibleSpace (normalizationSchemeOverField k p) := by
    obtain ⟨η, hη, _⟩ := hbir.bijOn.2.2 (by simp [genericPoints_eq_singleton] :
      genericPoint X ∈ genericPoints X)
    have hsingle : genericPoints (normalizationSchemeOverField k p) = {η} := by
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨hη, fun z hz => hbir.bijOn.2.1 hz hη ?_⟩
      have hz' : normalizationOverField k p z = genericPoint X := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hbir.bijOn.1 hz
      have hη' : normalizationOverField k p η = genericPoint X := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hbir.bijOn.1 hη
      exact hz'.trans hη'.symm
    refine (irreducibleSpace_def _).mpr ?_
    change IsIrreducible (Set.univ : Set (normalizationSchemeOverField k p))
    rw [← genericPoints.closure (α := normalizationSchemeOverField k p), hsingle]
    exact isIrreducible_singleton.closure
  let : IsIntegral (normalizationSchemeOverField k p) :=
    isIntegral_of_irreducibleSpace_of_isReduced _
  exact {}

/-- The normalization of a proper scheme over a field is proper over that field.

This is the first of the two assertions of [Stacks, Tag 0GK4]. The tag itself is carried by
`AlgebraicGeometry.isProper_and_isProjective_normalizationOverField`, which states both
assertions. -/
public theorem isProper_normalizationOverField_comp (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] :
    IsProper (normalizationOverField k p ≫ p) := by
  let : LocallyOfFiniteType p := IsProper.toLocallyOfFiniteType
  let := isFinite_normalizationOverField k p
  infer_instance

/-- **Stacks Project, Tag 0BXS.** The relative normalization of a scheme locally of finite type
over a field in a reduced scheme locally of finite type over the same field is finite, as soon as
the morphism between them is quasi-compact. -/
@[stacks 0BXS]
public theorem isFinite_fromNormalization_of_locallyOfFiniteType_over_field
    (k : Type u) [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    (f : Y ⟶ X) (hf : f ≫ pX = pY)
    [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
    [QuasiCompact f] [IsReduced Y] :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian pY
    letI : QuasiSeparated f := QuasiSeparated.of_comp f (terminal.from X)
    IsFinite f.fromNormalization := by
  subst pY
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian (f ≫ pX)
  let : QuasiSeparated f := QuasiSeparated.of_comp f (terminal.from X)
  apply isFinite_fromNormalization f (isNagataScheme_of_locallyOfFiniteType_over_field k pX)
  · intro U hU
    let : CompactSpace U := isCompact_iff_compactSpace.mp hU
    let : IsNoetherian U := AlgebraicGeometry.IsNoetherian.mk
    exact finite_irreducibleComponents_of_isNoetherian
  · intro x
    let := (f.residueFieldMap x.1).hom.toAlgebra
    rw [IntermediateField.fg_top_iff]
    apply RingHom.EssFiniteType.of_comp (pX.residueFieldMap (f x.1)).hom
    rw [← CommRingCat.hom_comp, ← Scheme.residueFieldMap_comp]
    exact (LocallyOfFiniteType.stalkMap (f ≫ pX) x.1).residueFieldMap

end AlgebraicGeometry

end
