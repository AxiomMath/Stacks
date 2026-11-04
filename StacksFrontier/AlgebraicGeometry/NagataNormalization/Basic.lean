module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.RingHom.EssFiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.NormalizationMono.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Normalization
public import StacksFrontier.RingTheory.Nagata.IntegralClosure

/-!
# Finiteness of normalization over a Nagata base

Let `f : X ⟶ S` be quasi-compact and quasi-separated with `X` reduced, suppose the quasi-compact
opens of `X` have finitely many irreducible components, suppose the residue field extension at
every generic point of an irreducible component of `X` is finitely generated, and suppose `S` is
Nagata. Then the relative normalization of `S` in `X` is finite over `S`.

Applied to the canonical morphism from the spectra of the residue fields at the generic points of
a scheme, this says that the normalization morphism of a Nagata scheme is finite; and since a
scheme locally of finite type over a field is Nagata, the normalization morphism of a locally
algebraic scheme over a field is finite and dominant.

## Main results

* `AlgebraicGeometry.isFinite_fromNormalization` is Tag 0AVK.
* `AlgebraicGeometry.isFinite_fromNormalization_of_locallyOfFiniteType` is Tag 03GR: the
  hypotheses of Tag 0AVK other than reducedness and Nagata-ness of the base are automatic for a
  morphism of finite type.
* `AlgebraicGeometry.Scheme.isFinite_normalization_of_isNagataScheme` is Tag 035S: the
  normalization morphism of a Nagata scheme is finite, with no hypothesis beyond Nagata-ness.
  `AlgebraicGeometry.Scheme.isFinite_normalization` is the same statement in the form that takes
  the finiteness of the irreducible components as an explicit input.
* `AlgebraicGeometry.isFinite_normalizationOverField` and
  `AlgebraicGeometry.isDominant_normalizationOverField`: the normalization morphism of a scheme
  locally of finite type over a field is finite and dominant. These are the first two of the
  three assertions of Tag 0BXR part (1).
## Implementation notes

The relative normalization is Mathlib's `AlgebraicGeometry.Scheme.Hom.normalization`, whose
structural morphism to the base is `AlgebraicGeometry.Scheme.Hom.fromNormalization`. Finiteness
is checked directly against the definition of `AlgebraicGeometry.IsFinite`, whose two components
are affineness of the morphism — already known, the structural morphism being integral — and
finiteness of the ring map on the sections over every affine open. The latter is
`AlgebraicGeometry.Scheme.Hom.fromNormalization_app`, which identifies that ring map, up to the
isomorphism `AlgebraicGeometry.Scheme.Hom.normalizationObjIso`, with the inclusion of the base
sections into their integral closure. No Zariski-local gluing argument is therefore needed.

The source's argument for Tag 0AVK is the inclusion of `Γ(X, f⁻¹U)` into the product of the
residue fields at the generic points of `f⁻¹U`: there are finitely many of them, each residue
field is essentially of finite type over `Γ(S, U)` by the finite-generation hypothesis, so each
integral closure of `Γ(S, U)` in it is a finite module over the Noetherian ring `Γ(S, U)`, and
the integral closure of `Γ(S, U)` in `Γ(X, f⁻¹U)` embeds in the product of those. Injectivity of
that embedding is exactly the statement that a section of a reduced scheme vanishing at every
generic point in its domain is zero.

For Tag 035S the morphism `f` is the canonical one from the spectra of the residue fields at the
generic points. Its source is reduced and it is surjective on stalks; both are the
instances `AlgebraicGeometry.Scheme.genericPointResidueSpectrum_isReduced` and
`AlgebraicGeometry.Scheme.surjectiveOnStalks_fromGenericPointResidueFields`. Being surjective on
stalks makes every residue-field map surjective, hence every residue field extension finitely
generated, which is the last hypothesis of Tag 0AVK. The remaining hypothesis of Tag 0AVK, that
the quasi-compact opens have finitely many irreducible components, also follows from Nagata-ness:
a Nagata scheme is locally Noetherian, so its quasi-compact opens are Noetherian spaces. Since
that fact is needed to form the normalization morphism at all, it appears in the statement of
Tag 035S as the proof term supplied to `AlgebraicGeometry.Scheme.normalization`.

Tag 0BXR part (1) is stated for an arbitrary morphism to `Spec k` that is locally of finite type,
rather than for an object of the category over `Spec k`; for `X : Over (Spec (.of k))` with
`LocallyOfFiniteType X.hom` it applies to `X.hom`. The third assertion of part (1), that the
normalization is a disjoint union of normal irreducible locally algebraic schemes, is not proved
here, so the tag is withheld.

Tag 03GR is the special case of Tag 0AVK for a morphism of finite type. Finite type is expressed
by `AlgebraicGeometry.LocallyOfFiniteType` together with `AlgebraicGeometry.QuasiCompact`, and the
two remaining hypotheses of Tag 0AVK are then automatic: the source is locally Noetherian over the
locally Noetherian base, so its quasi-compact opens are Noetherian schemes and have finitely many
irreducible components; and a morphism of finite type induces residue field extensions that are
essentially of finite type, hence finitely generated as field extensions. Local Noetherianity of
the base, which Mathlib's relative normalization needs in order to know that the morphism is
quasi-separated, is not an extra assumption but a consequence of Nagata-ness; since
`IsNagataScheme` is not a class it is introduced in the statement itself.

## References

* [Stacks Project, Tag 0AVK](https://stacks.math.columbia.edu/tag/0AVK)
* [Stacks Project, Tag 03GR](https://stacks.math.columbia.edu/tag/03GR)
* [Stacks Project, Tag 035S](https://stacks.math.columbia.edu/tag/035S)
* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.Normalization (finite_irreducibleComponents_of_isNagataScheme)

namespace AlgebraicGeometry

universe u

/-! ### Finiteness of the relative normalization -/

/-- Finiteness of the structural morphism of the relative normalization, from finiteness of the
integral closures on affine charts of the base. -/
theorem isFinite_fromNormalization_of_module_finite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (H : ∀ U : Y.affineOpens, letI := (f.app U.1).hom.toAlgebra
      Module.Finite Γ(Y, U.1) (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1))) :
    IsFinite f.fromNormalization := by
  rw [isFinite_iff]
  refine ⟨inferInstance, fun U hU => ?_⟩
  let := (f.app U).hom.toAlgebra
  rw [f.fromNormalization_app hU, CommRingCat.hom_comp]
  exact RingHom.Finite.comp
    (RingHom.Finite.of_surjective _
      ((ConcreteCategory.bijective_of_isIso (f.normalizationObjIso hU).inv).2))
    (RingHom.finite_algebraMap.mpr (H ⟨U, hU⟩))

/-- A section of a reduced scheme that vanishes at every generic point of the scheme lying in its
domain of definition is zero. -/
private theorem eq_zero_of_evaluation_genericPoints_eq_zero {X : Scheme.{u}} [IsReduced X]
    {U : X.Opens} (s : Γ(X, U))
    (hs : ∀ (η : genericPoints X) (hη : η.1 ∈ U), X.evaluation U η.1 hη s = 0) :
    s = 0 := by
  refine eq_zero_of_basicOpen_eq_bot s ((Opens.not_nonempty_iff_eq_bot _).mp fun h => ?_)
  obtain ⟨η, hηs, hη⟩ := (dense_iff_closure_eq.mpr genericPoints.closure).inter_open_nonempty _
    (X.basicOpen s).isOpen h
  exact (X.evaluation_eq_zero_iff_notMem_basicOpen η (X.basicOpen_le s hηs) s).mp
    (hs ⟨η, hη⟩ (X.basicOpen_le s hηs)) hηs

/-- Evaluating sections over an affine open at a point of it is essentially of finite type: it is
the germ map, a localization, followed by the surjection onto the residue field. -/
private theorem essFiniteType_evaluation {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    (X.evaluation U x hx).hom.EssFiniteType := by
  let := (X.presheaf.germ U x hx).hom.toAlgebra
  have := hU.isLocalization_stalk ⟨x, hx⟩
  have hg : (X.presheaf.germ U x hx).hom.EssFiniteType :=
    Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  exact hg.comp (RingHom.FiniteType.of_surjective _ (X.residue_surjective x)).essFiniteType

/-- The residue field extension is finitely generated as soon as the residue field map is
essentially of finite type. -/
private theorem fg_top_of_essFiniteType_residueFieldMap {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (h : (f.residueFieldMap x).hom.EssFiniteType) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    (⊤ : IntermediateField (S.residueField (f x)) (X.residueField x)).FG := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have : Algebra.EssFiniteType (S.residueField (f x)) (X.residueField x) := by
    rwa [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
  exact IntermediateField.fg_top _ _

/-- **Stacks Project, Tag 0AVK.** Let `f : X ⟶ S` be quasi-compact and quasi-separated with `X`
reduced. If the quasi-compact opens of `X` have finitely many irreducible components, the residue
field extension at every generic point of an irreducible component of `X` is finitely generated,
and `S` is Nagata, then the normalization of `S` in `X` is finite over `S`. -/
@[stacks 0AVK]
theorem isFinite_fromNormalization
    {X S : Scheme.{u}} (f : X ⟶ S) (hS : IsNagataScheme S)
    [QuasiCompact f] [QuasiSeparated f] [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hκ : ∀ x : genericPoints X,
      letI := (f.residueFieldMap x.1).hom.toAlgebra
      (⊤ : IntermediateField (S.residueField (f x.1)) (X.residueField x.1)).FG) :
    IsFinite f.fromNormalization := by
  refine isFinite_fromNormalization_of_module_finite f fun U => ?_
  let := (f.app U.1).hom.toAlgebra
  have hR : IsNagataRing Γ(S, U.1) := hS.isNagataRing_sections U
  have : IsNoetherianRing Γ(S, U.1) := hR.1
  let I := {η : genericPoints X // η.1 ∈ f ⁻¹ᵁ U.1}
  have : Finite (genericPoints ((f ⁻¹ᵁ U.1 : X.Opens) : Set X)) :=
    (genericPoints.finite (hX _ (f.isCompact_preimage U.2.isCompact))).to_subtype
  have : Finite I :=
    Finite.of_injective (Scheme.genericPointsInOpenEquiv X (f ⁻¹ᵁ U.1))
      (Scheme.genericPointsInOpenEquiv X (f ⁻¹ᵁ U.1)).injective
  let : ∀ η : I, Algebra Γ(S, U.1) (X.residueField η.1.1) := fun η ↦
    ((X.evaluation (f ⁻¹ᵁ U.1) η.1.1 η.2).hom.comp (f.app U.1).hom).toAlgebra
  let φ (η : I) : Γ(X, f ⁻¹ᵁ U.1) →ₐ[Γ(S, U.1)] X.residueField η.1.1 :=
    { __ := (X.evaluation (f ⁻¹ᵁ U.1) η.1.1 η.2).hom
      commutes' := fun _ ↦ rfl }
  have hfinite (η : I) :
      Module.Finite Γ(S, U.1) (integralClosure Γ(S, U.1) (X.residueField η.1.1)) := by
    have : Algebra.EssFiniteType Γ(S, U.1) (X.residueField η.1.1) := by
      show ((X.evaluation (f ⁻¹ᵁ U.1) η.1.1 η.2).hom.comp (f.app U.1).hom).EssFiniteType
      rw [← CommRingCat.hom_comp, ← Scheme.evaluation_naturality f η.1.1 η.2]
      let := (f.residueFieldMap η.1.1).hom.toAlgebra
      exact (essFiniteType_evaluation U.2 (f η.1.1) η.2).comp
        (IntermediateField.fg_top_iff.mp (hκ η.1))
    exact IsIntegralClosure.finite_of_essFiniteType_of_isReduced
      (S := X.residueField η.1.1) hR.2
  have : Module.Finite Γ(S, U.1)
      (∀ η : I, integralClosure Γ(S, U.1) (X.residueField η.1.1)) :=
    Module.Finite.pi (h := hfinite)
  refine Module.Finite.of_injective
    (LinearMap.pi fun η : I ↦ (φ η).mapIntegralClosure.toLinearMap) fun a b hab =>
      Subtype.ext (sub_eq_zero.mp (eq_zero_of_evaluation_genericPoints_eq_zero _ fun η hη => ?_))
  simpa [φ, map_sub, sub_eq_zero] using congrArg Subtype.val (congrFun hab (⟨η, hη⟩ : I))

/-- **Stacks Project, Tag 03GR.** Let `f : X ⟶ S` be of finite type with `X` reduced and `S`
Nagata. Then the normalization of `S` in `X` is finite over `S`. -/
@[stacks 03GR]
theorem isFinite_fromNormalization_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : IsNagataScheme S) [LocallyOfFiniteType f] [QuasiCompact f] [IsReduced X] :
    haveI : IsLocallyNoetherian S :=
      ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme S).mp hS).1
    IsFinite f.fromNormalization := by
  have : IsLocallyNoetherian S :=
    ((isNagataScheme_iff_isLocallyNoetherian_and_isUniversallyJapaneseScheme S).mp hS).1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine isFinite_fromNormalization f hS (fun U hU => ?_) fun x => ?_
  · have : IsNoetherian U :=
      { toIsLocallyNoetherian := inferInstance
        toCompactSpace := isCompact_iff_compactSpace.mp hU }
    exact finite_irreducibleComponents_of_isNoetherian
  · exact fg_top_of_essFiniteType_residueFieldMap f x.1
      (RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f x.1))

/-! ### The normalization of a Nagata scheme -/

namespace Scheme

/-- The normalization morphism of a Nagata scheme is finite.

The finiteness hypothesis on the irreducible components of the quasi-compact opens serves only
to form the normalization morphism, and is itself a consequence of the Nagata hypothesis; see
`AlgebraicGeometry.Scheme.isFinite_normalization_of_isNagataScheme`. -/
theorem isFinite_normalization {X : Scheme.{u}} (hNagata : IsNagataScheme X)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsFinite (X.normalization hX) := by
  let f := fromGenericPointResidueFields X
  let : QuasiCompact f := quasiCompactFromGenericPointResidueFields X hX
  let : QuasiSeparated f := quasiSeparatedFromGenericPointResidueFields X
  show IsFinite f.fromNormalization
  refine isFinite_fromNormalization f hNagata
    (genericPointResidueSpectrum_finite_irreducibleComponents X) fun x => ?_
  exact fg_top_of_essFiniteType_residueFieldMap f x.1 (RingHom.FiniteType.of_surjective _
    (AlgebraicGeometry.surjective_residueFieldMap_of_surjectiveOnStalks f x.1)).essFiniteType

/-- **Stacks Project, Tag 035S.** The normalization morphism `ν : X^ν ⟶ X` of a Nagata scheme
`X` is finite.

A Nagata scheme is locally Noetherian, so each of its quasi-compact opens is a Noetherian space
and has finitely many irreducible components; the Nagata hypothesis therefore both forms the
normalization morphism and makes it finite. -/
@[stacks 035S]
theorem isFinite_normalization_of_isNagataScheme {X : Scheme.{u}} (hNagata : IsNagataScheme X) :
    IsFinite (X.normalization (finite_irreducibleComponents_of_isNagataScheme X hNagata)) :=
  isFinite_normalization hNagata _

end Scheme

/-! ### The normalization of a locally algebraic scheme over a field -/

/-- **Stacks Project, Tag 0BXR part (1), finiteness.** The normalization morphism of a scheme
locally of finite type over a field is finite.

The tag is withheld: part (1) also asserts that the normalization is a disjoint union of normal
irreducible locally algebraic schemes, which is not proved here. -/
theorem isFinite_normalizationOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsFinite (normalizationOverField k p) :=
  Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType_over_field k p)
    (finite_irreducibleComponents_of_locallyOfFiniteType k p)

/-- **Stacks Project, Tag 0BXR part (1), dominance.** The normalization morphism of a scheme
locally of finite type over a field is dominant.

The tag is withheld for the same reason as for `isFinite_normalizationOverField`. -/
theorem isDominant_normalizationOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsDominant (normalizationOverField k p) := by
  let f := Scheme.fromGenericPointResidueFields X
  let hX := finite_irreducibleComponents_of_locallyOfFiniteType k p
  let : QuasiCompact f := Scheme.quasiCompactFromGenericPointResidueFields X hX
  let : QuasiSeparated f := Scheme.quasiSeparatedFromGenericPointResidueFields X
  show IsDominant f.fromNormalization
  exact Stacks.AlgebraicGeometry.Normalization.isDominant_fromNormalization f

end AlgebraicGeometry

end
