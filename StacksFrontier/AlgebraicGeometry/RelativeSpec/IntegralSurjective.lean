module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability

@[expose] public section

/-!
# When the relative spectrum is integral and surjective over the base

Let `s` be a relative-spectrum situation, that is, a scheme `S` together with a quasi-coherent
sheaf of commutative `𝒪_S`-algebras `A`, and let `π : Spec_S(A) ⟶ S` be the structure morphism
of its relative spectrum. This file records the two affine-local criteria for `π`:

* `π` is **integral** as soon as `A(U)` is integral over `Γ(S, U)` for every affine open `U`;
* `π` is **surjective** as soon as `Spec A(U) ⟶ Spec Γ(S, U)` is surjective for every affine
  open `U`.

Both are the statements one wants when the algebra is given by an affine-local construction, as
for instance the algebra `𝒪_S ⊕ ℐ` of
`StacksFrontier/RingTheory/ModuleQuadraticExtension.lean`, whose sections over every affine open
are integral over the base by
`Stacks.ModuleQuadraticExtension.Ext.isIntegral` and have surjective spectrum by
`Stacks.ModuleQuadraticExtension.Ext.exists_isPrime_comap_eq`.

## Main results

* `Stacks.RelativeSpec.isIntegralHom_toBase_of_isIntegral_app`
* `Stacks.RelativeSpec.surjective_toBase_of_surjective_specSectionsToOpen`
* `Stacks.RelativeSpec.surjective_toBase_of_surjective_specMap_app`

## Implementation notes

The integrality criterion is the argument of
`Stacks.RelativeSpec.isIntegralHom_toBase`, which proves exactly this for the algebra
`f_* 𝒪_X` of a universally closed `f`, with its one hypothesis — integrality of the sections of
the algebra's structure morphism — abstracted out. Affineness is
`Stacks.AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase`; over an affine open `U` the
sections of `π` are those of the structure morphism of `A` followed by the universal map
(`Stacks.RelativeSpec.toBase_app`), which is an isomorphism there
(`Stacks.RelativeSpec.isIso_universalAlgebraMap_app`), so integrality transfers along it.

The surjectivity criterion does **not** go through locality at the target. A chart followed by
`π` is `Stacks.RelativeSpec.specSectionsToOpen` followed by the inclusion of its affine open
(`Stacks.RelativeSpec.GluedSpectrum.chart_comp_toBase`), so the image of `π` contains every
affine open whose `specSectionsToOpen` is surjective; the affine opens cover the base, which
finishes it. That is shorter than identifying `π ∣_ U` with a chart.

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LQ](https://stacks.math.columbia.edu/tag/01LQ)
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.RelativeSpec

variable (s : RelativeSpecSituation.{u})

/-- **The relative spectrum of a quasi-coherent algebra whose sections are integral over the
base is integral over the base.** -/
theorem isIntegralHom_toBase_of_isIntegral_app
    (h : ∀ U : s.base.Opens, IsAffineOpen U →
      (s.algebra.hom.hom.app (.op U)).hom.IsIntegral) :
    IsIntegralHom (gluedSpectrum s).toBase := by
  have _ : IsAffineHom (gluedSpectrum s).toBase :=
    AffineAlgebraEquivalence.isAffineHom_relativeSpecToBase s.algebra
  have _ : (RingHom.toMorphismProperty RingHom.IsIntegral).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  refine ⟨fun U hU => ?_⟩
  have _ := isIso_universalAlgebraMap_app s ⟨U, hU⟩
  rw [toBase_app]
  exact MorphismProperty.RespectsIso.postcomp
    (RingHom.toMorphismProperty RingHom.IsIntegral) _ _ (h U hU)

/-- **The relative spectrum of a quasi-coherent algebra is surjective over the base as soon as
each of the morphisms `Spec A(U) ⟶ U` is.** -/
theorem surjective_toBase_of_surjective_specSectionsToOpen
    (h : ∀ U : s.base.affineOpens, Function.Surjective (specSectionsToOpen s U).base) :
    Surjective (gluedSpectrum s).toBase := by
  refine ⟨fun y => ?_⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    s.base.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  obtain ⟨z, hz⟩ := h ⟨U, hU⟩ ⟨y, hyU⟩
  refine ⟨((gluedSpectrum s).chart ⟨U, hU⟩).base z, ?_⟩
  have h1 : (gluedSpectrum s).toBase (((gluedSpectrum s).chart ⟨U, hU⟩) z)
      = Scheme.Opens.ι U ((specSectionsToOpen s ⟨U, hU⟩) z) :=
    congrArg (fun m : Spec (s.algebra.sections (⟨U, hU⟩ : s.base.affineOpens).1) ⟶ s.base => m z)
      (GluedSpectrum.chart_comp_toBase (gluedSpectrum s) ⟨U, hU⟩)
  exact h1.trans (congrArg (Scheme.Opens.ι U) hz)

/-- **The relative spectrum of a quasi-coherent algebra is surjective over the base as soon as
the spectrum of its sections over each affine open surjects onto that affine open's
spectrum.** -/
theorem surjective_toBase_of_surjective_specMap_app
    (h : ∀ U : s.base.affineOpens,
      Surjective (Spec.map (s.algebra.hom.hom.app (.op U.1)))) :
    Surjective (gluedSpectrum s).toBase := by
  refine surjective_toBase_of_surjective_specSectionsToOpen s fun U => ?_
  exact (inferInstance : Surjective U.2.isoSpec.inv).surj.comp (h U).surj

end Stacks.RelativeSpec

end
