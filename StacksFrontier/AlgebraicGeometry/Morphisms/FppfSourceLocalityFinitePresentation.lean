module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FppfSourceLocality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local finite presentation is local on the source for the fppf topology of schemes

## Main results

* `AlgebraicGeometry.LocallyOfFinitePresentation.isLocalAtSource_fppfPrecoverage`: being locally
  of finite presentation is local on the source for the fppf topology of schemes.

## References

* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 036N](https://stacks.math.columbia.edu/tag/036N)
* [Stacks Project, Tag 02KK](https://stacks.math.columbia.edu/tag/02KK)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Being locally of finite presentation is local on the source for the fppf topology of
schemes. -/
@[ega "IV 11.3.16" "partial",
  sga "3 V 9.1" "partial",
  sga "3 VIB 10.8" "partial",
  sga "4 IV 8.5.5" "partial"]
instance LocallyOfFinitePresentation.isLocalAtSource_fppfPrecoverage :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) Scheme.fppfPrecoverage :=
  let : MorphismProperty.RespectsLeft
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) :=
    { precomp := fun i hi f hf => by
        have : LocallyOfFinitePresentation i := hi.2
        have : LocallyOfFinitePresentation f := hf
        exact inferInstance }
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  let : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyOfFinitePresentation.{u}) (Q := RingHom.FinitePresentation)
  isLocalAtSource_fppf_of_affine_descent (@LocallyOfFinitePresentation.{u})
    fun {_X' _X _Y} _ _ _ g f hg hgflat hglfp hcomp => by
      have : Surjective g := hg
      have : Flat g := hgflat
      have : LocallyOfFinitePresentation g := hglfp
      have : LocallyOfFinitePresentation (g ≫ f) := hcomp
      rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
      refine RingHom.finitePresentation_of_comp_of_faithfullyFlat
        f.appTop.hom g.appTop.hom ?_ ?_ (Scheme.Hom.finitePresentation_appTop g)
      · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
          Scheme.Hom.finitePresentation_appTop (g ≫ f)
      · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
          ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry

end
