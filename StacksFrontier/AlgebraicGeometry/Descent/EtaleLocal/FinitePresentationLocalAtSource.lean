module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality

/-!
# Local finite presentation is étale local on the source

Being locally of finite presentation is local on the source for the étale topology, and hence
étale local on the source and target: the case of Tag 04R3 for morphisms locally of finite
presentation.

## Main results

* `AlgebraicGeometry.LocallyOfFinitePresentation.isLocalAtSource_etalePrecoverage`: being
  locally of finite presentation is local on the source for the étale topology.
* `AlgebraicGeometry.LocallyOfFinitePresentation.respectsRight_etale`: postcomposition with an
  étale morphism preserves local finite presentation.
* `AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget`: being locally of
  finite presentation is étale local on the source and target.

## References

* [Stacks Project, Tag 02KK](https://stacks.math.columbia.edu/tag/02KK)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Being locally of finite presentation is local on the source for the étale topology. -/
instance LocallyOfFinitePresentation.isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.etalePrecoverage :=
  letI : MorphismProperty.RespectsLeft
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    { precomp := fun i hi f hf => by
        have : Etale i := hi
        have : LocallyOfFinitePresentation f := hf
        exact inferInstance }
  letI : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  letI : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyOfFinitePresentation.{u}) (Q := RingHom.FinitePresentation)
  isLocalAtSource_etale_of_affine_descent (@LocallyOfFinitePresentation.{u})
    fun {_X' _X _Y} _ _ _ g f hg hg' hcomp => by
      have : Surjective g := hg
      have : Etale g := hg'
      have : LocallyOfFinitePresentation (g ≫ f) := hcomp
      rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
      refine RingHom.finitePresentation_of_comp_of_faithfullyFlat
        f.appTop.hom g.appTop.hom ?_ ?_ (Scheme.Hom.finitePresentation_appTop g)
      · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
          Scheme.Hom.finitePresentation_appTop (g ≫ f)
      · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
          ⟨inferInstance, inferInstance⟩

/-- Postcomposition with an étale morphism preserves local finite presentation. -/
@[ega "IV 1.4.3" "(ii)"]
theorem LocallyOfFinitePresentation.respectsRight_etale :
    MorphismProperty.RespectsRight
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) where
  postcomp i hi f hf := by
    have : Etale i := hi
    have : LocallyOfFinitePresentation f := hf
    exact inferInstance

/-- Being a morphism of schemes locally of finite presentation is étale local on the source and
target. -/
@[stacks 04R3 "locally_finite_presentation"]
theorem LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  let := LocallyOfFinitePresentation.respectsRight_etale.{u}
  IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource _

end AlgebraicGeometry

end
