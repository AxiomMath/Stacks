module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionQcqs
public import
  StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.TwistedInverseImageRestrictionSupport

/-!
# Tag 0A9N part (2) for quasi-compact quasi-separated schemes, with every input discharged

`Stacks.Duality.OpenImmersion.twistedInverseImage_cohomologySupportedOn_iff_isIso_restrictionMap`
is [Stacks, Tag 0A9N] part (2) for an arbitrary cartesian square along an open immersion, with
the inputs of [Stacks, Tag 0A9L] as arguments. This file reads it in the source's situation — a
morphism `f : X ⟶ Y` of quasi-compact and quasi-separated schemes, a quasi-compact open `V ⊆ Y`
and `U = f⁻¹(V)` — where every one of those inputs is proved, for the comparison
`Stacks.Duality.OpenImmersion.qcqsTwistedInverseImageRestrictionMap` that carries Tag 0A9L.

## Main results

* `Stacks.Duality.OpenImmersion.qcqs_cohomologySupportedOn_iff_isIso_restrictionMap` — for every
  `Q ∈ D_QCoh(𝒪_Y)` supported on `Y ∖ V` the object `a(Q)` is supported on `X ∖ U` iff the
  comparison `(j')^* ∘ a ⟶ a' ∘ j^*` of Tag 0A9L is an isomorphism on all of `D_QCoh(𝒪_Y)`.

## References

* [Stacks Project, Tag 0A9N](https://stacks.math.columbia.edu/tag/0A9N)
* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality.OpenImmersion

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] (V : Y.Opens) [CompactSpace V]

/-- **[Stacks, Tag 0A9N], part (2), at the source's hypotheses, with nothing carried.** Let
`f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes, let `a` be the right
adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, let `V ⊆ Y` be a quasi-compact open with inverse
image `U = f⁻¹(V)`. Then for every `Q ∈ D_QCoh(𝒪_Y)` supported on `Y ∖ V` the image `a(Q)` is
supported on `X ∖ U` if and only if the comparison of [Stacks, Tag 0A9L] is an isomorphism on all
`K` in `D_QCoh(𝒪_Y)`. -/
@[stacks 0A9N "part (2)"]
theorem qcqs_cohomologySupportedOn_iff_isIso_restrictionMap :
    (∀ Q : quasiCoherentDerivedCategory Y,
        Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn Y.ringCatSheaf
            (Set.range V.ι.base)ᶜ Q.obj →
          Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn X.ringCatSheaf
            (Set.range (f ⁻¹ᵁ V).ι.base)ᶜ
            ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              Q).obj) ↔
      (∀ K : quasiCoherentDerivedCategory Y,
        IsIso ((qcqsTwistedInverseImageRestrictionMap f V).app K)) :=
  twistedInverseImage_cohomologySupportedOn_iff_isIso_restrictionMap (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedRestrict _)
    (isQuasicoherent_homology_derivedRestrict _)
    (isPullback_morphismRestrict f V).flip

end Stacks.Duality.OpenImmersion

end
