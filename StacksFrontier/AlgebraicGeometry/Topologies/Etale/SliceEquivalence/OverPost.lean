module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization

/-!
# Every slice functor of composition with an étale morphism is an equivalence

Let `B` be a big étale site, `X` a scheme in it and `j : U ⟶ X` an object of the small étale
site of `X`. Composition with `j` is the site functor
`AlgebraicGeometry.smallEtalePostcompose`, and it is *not* full in general: a morphism over `X`
between two étale schemes over `U` need not commute with the two structure morphisms to `U`,
and the library's `AlgebraicGeometry.full_smallEtalePostcompose` accordingly asks that `j` be a
monomorphism.

Its *slice* functors are nevertheless equivalences, with no hypothesis on `j`. Over a fixed
étale scheme `W` over `U`, a morphism to `W` over `X` already determines the arrow to `U`, by
composing with `W ⟶ U`; so the obstruction to fullness disappears, and an étale scheme over `X`
equipped with an arrow to `W` over `X` is étale over `U` through that arrow. This is the
condition `[∀ x, (CategoryTheory.Over.post x).IsEquivalence]` under which
`Stacks.ModuleLowerShriek.pullbackCompToPresheafIso` identifies the underlying abelian presheaf
of lower shriek on presheaves of modules with the left Kan extension of the underlying abelian
presheaf — the comparison of Stacks 0798, which
`Stacks.SheafOfModules.lowerShriekForget_not_isomorphic` shows fails for a general site functor.

## Main results

* `AlgebraicGeometry.full_overPost_smallEtalePostcompose`,
  `AlgebraicGeometry.essSurj_overPost_smallEtalePostcompose` and
  `AlgebraicGeometry.isEquivalence_overPost_smallEtalePostcompose` — the slice functors of
  composition with `j` are full, essentially surjective, and hence equivalences.

## Implementation notes

Fullness and essential surjectivity are proved by hand rather than deduced from Mathlib's
instances for `CategoryTheory.Over.post`, which require the functor itself to be full and
essentially surjective; `AlgebraicGeometry.smallEtalePostcompose` is neither. Faithfulness does
come from Mathlib's instance, `AlgebraicGeometry.faithful_smallEtalePostcompose` being
unconditional.

Objects of the small étale site are `CategoryTheory.ObjectProperty.FullSubcategory` objects of a
slice, so a morphism is built as an `CategoryTheory.ObjectProperty.homMk` of an
`CategoryTheory.Over.homMk` and two extensionality lemmas are needed to compare two of them.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX) (W : SmallEtale B U.obj.left.1 U.obj.left.property)

/-- **The slice functors of composition with `U ⟶ X` are full.** A morphism over `X` between
two étale schemes over `W` commutes with their structure morphisms to `U`, because those
factor through `W ⟶ U`. The functor itself is full only when `U ⟶ X` is a monomorphism. -/
public instance full_overPost_smallEtalePostcompose :
    (Over.post (X := W) (smallEtalePostcompose B X hX U)).Full where
  map_surjective {a b} φ := by
    let m : a.left.obj.left ⟶ b.left.obj.left := φ.left.hom.left
    have hw : m ≫ b.hom.hom.left = a.hom.hom.left :=
      congrArg (fun k => k.hom.left) (Over.w φ)
    have hu : m ≫ b.left.obj.hom = a.left.obj.hom := by
      rw [← Over.w b.hom.hom, ← Category.assoc, hw, Over.w a.hom.hom]
    refine ⟨Over.homMk (ObjectProperty.homMk (Over.homMk m hu)) ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact hw
    · apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      rfl

/-- **The slice functors of composition with `U ⟶ X` are essentially surjective.** An étale
scheme over `X` with an arrow to `W` over `X` is étale over `U` through that arrow, `W ⟶ U`
being étale, and it is carried to itself. -/
public instance essSurj_overPost_smallEtalePostcompose :
    (Over.post (X := W) (smallEtalePostcompose B X hX U)).EssSurj where
  mem_essImage Y := by
    have hfac : (Y.hom.hom.left ≫ W.obj.hom) ≫ U.obj.hom = Y.left.obj.hom :=
      (Category.assoc _ _ _).trans (Over.w Y.hom.hom)
    have hetale : Etale (B.inclusion.map (Y.hom.hom.left ≫ W.obj.hom)) :=
      B.etale_map_of_postcomp _ U.obj.hom Y.left.obj.hom Y.left.property U.property hfac
    let Z : SmallEtale B U.obj.left.1 U.obj.left.property :=
      ⟨Over.mk (Y.hom.hom.left ≫ W.obj.hom), hetale⟩
    let z : Z ⟶ W := ObjectProperty.homMk (Over.homMk Y.hom.hom.left rfl)
    refine ⟨Over.mk z, ⟨Over.isoMk (ObjectProperty.isoMk _
      (Over.isoMk (Iso.refl Y.left.obj.left) ?_)) ?_⟩⟩
    · exact (Category.id_comp _).trans hfac.symm
    · apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      exact Category.id_comp _

/-- **Every slice functor of composition with `U ⟶ X` is an equivalence.** This is the
hypothesis under which `Stacks.ModuleLowerShriek.pullbackCompToPresheafIso` holds. -/
public instance isEquivalence_overPost_smallEtalePostcompose :
    (Over.post (X := W) (smallEtalePostcompose B X hX U)).IsEquivalence where

end AlgebraicGeometry

end
