module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-affine morphisms

A morphism of schemes is quasi-affine when the inverse image of every affine open subscheme of
the target is a quasi-affine scheme. Such a morphism is separated and quasi-compact. For an
affine source, quasi-affineness is equivalent to quasi-compactness, and every morphism out of a
quasi-affine scheme into a quasi-separated scheme is quasi-affine.

## Main definitions

* `AlgebraicGeometry.IsQuasiAffineHom` is the property that a morphism of schemes is
  quasi-affine.

## Main results

* `AlgebraicGeometry.isSeparated_of_isQuasiAffineHom`: a quasi-affine morphism is separated.
* `AlgebraicGeometry.quasiCompact_of_isQuasiAffineHom`: a quasi-affine morphism is quasi-compact.
* `AlgebraicGeometry.isQuasiAffineHom_iff_quasiCompact` characterizes quasi-affine morphisms
  with affine source.
* `AlgebraicGeometry.isQuasiAffineHom_of_isQuasiAffine_of_quasiSeparatedSpace`: every morphism
  from a quasi-affine scheme to a quasi-separated scheme is quasi-affine.

## References

* [Stacks Project, Tag 01SK](https://stacks.math.columbia.edu/tag/01SK)
* [Stacks Project, Tag 01SL](https://stacks.math.columbia.edu/tag/01SL)
* [Stacks Project, Tag 01SP](https://stacks.math.columbia.edu/tag/01SP)
* [Stacks Project, Tag 054G](https://stacks.math.columbia.edu/tag/054G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is quasi-affine if the inverse image of every affine open subscheme of
the target is a quasi-affine scheme. -/
@[mk_iff, stacks 01SK] class IsQuasiAffineHom {X S : Scheme} (f : X ⟶ S) : Prop where
  isQuasiAffine_preimage : ∀ U : S.Opens, IsAffineOpen U → Scheme.IsQuasiAffine (f ⁻¹ᵁ U)

/-- A quasi-affine morphism of schemes is separated. -/
@[stacks 01SL "separated", ega "II 1.2.4" "more general", ega "II 5.1.6" "partial"]
instance isSeparated_of_isQuasiAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsQuasiAffineHom f] : IsSeparated f := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsSeparated)
    (U := fun i : S.affineOpens => (i : S.Opens)) (iSup_affineOpens_eq_top S)]
  intro i
  have : Scheme.IsQuasiAffine (f ⁻¹ᵁ (i : S.Opens)).toScheme :=
    IsQuasiAffineHom.isQuasiAffine_preimage (f := f) i i.2
  apply (IsSeparated.comp_iff (f := f ∣_ (i : S.Opens))
    (g := terminal.from (i : S.Opens).toScheme)).mp
  rw [terminal.comp_from]
  infer_instance

/-- A quasi-affine morphism of schemes is quasi-compact. -/
@[stacks 01SL "quasi-compact"]
instance quasiCompact_of_isQuasiAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsQuasiAffineHom f] : QuasiCompact f := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  exact fun U hU ↦ isCompact_iff_compactSpace.mpr
    (IsQuasiAffineHom.isQuasiAffine_preimage U hU).toCompactSpace

/-- A morphism from an affine scheme is quasi-affine if and only if it is quasi-compact. -/
@[stacks 01SP "characterization"]
theorem isQuasiAffineHom_iff_quasiCompact {X S : Scheme.{u}} [IsAffine X]
    (f : X ⟶ S) : IsQuasiAffineHom f ↔ QuasiCompact f := by
  refine ⟨fun _ ↦ inferInstance, fun hf ↦ ⟨fun U hU ↦ ?_⟩⟩
  have : CompactSpace (f ⁻¹ᵁ U).toScheme :=
    isCompact_iff_compactSpace.mp (quasiCompact_iff_forall_isAffineOpen.mp hf U hU)
  exact Scheme.IsQuasiAffine.of_isImmersion (f ⁻¹ᵁ U).ι

/-- Every morphism from a quasi-affine scheme to a quasi-separated scheme is quasi-affine. -/
@[stacks 01SP "quasi-separated target",
  stacks 054G "absolute corollary",
  ega "II 5.1.8" "X q-affine ⇒ f q-affine"]
instance isQuasiAffineHom_of_isQuasiAffine_of_quasiSeparatedSpace
    {X S : Scheme.{u}} [Scheme.IsQuasiAffine X] [QuasiSeparatedSpace S]
    (f : X ⟶ S) : IsQuasiAffineHom f := by
  refine ⟨fun U hU ↦ ?_⟩
  have : IsAffine U.toScheme := hU
  have : CompactSpace (f ⁻¹ᵁ U).toScheme := QuasiCompact.compactSpace_of_compactSpace (f ∣_ U)
  exact Scheme.IsQuasiAffine.of_isImmersion (f ⁻¹ᵁ U).ι

end AlgebraicGeometry
