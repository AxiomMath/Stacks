module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothSourceLocality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finiteness conditions are local on the source for the smooth topology of schemes

Being locally of finite type and being locally of finite presentation are local on the source for
the smooth topology of schemes. Both are instances of the smooth case of **Stacks 036H**,
`AlgebraicGeometry.isLocalAtSource_smooth_of_affine_descent`.

Three of the four hypotheses are formal: a smooth morphism is locally of finite presentation and
hence locally of finite type, so precomposition with a smooth morphism preserves either property
by stability under composition, and both are Zariski local on the source and on the target
through Mathlib's `AlgebraicGeometry.HasRingHomProperty` machinery for `RingHom.FiniteType` and
`RingHom.FinitePresentation`.

The fourth hypothesis is descent along a surjective smooth morphism of affine schemes, and it is
the only mathematical content. It reads on global sections as a statement about ring maps
`R → A → B` with `A → B` faithfully flat and of finite presentation: that `R → A` is of finite
type if `R → B` is (**Stacks 0367**), and of finite presentation if `R → B` is (**Stacks 02KK**).
The two hypotheses on `A → B` are what a surjective smooth morphism of affines gives: flat and
surjective is faithfully flat on global sections, a smooth morphism being flat, and a smooth
morphism is of finite presentation.

## Main results

* `AlgebraicGeometry.LocallyOfFiniteType.isLocalAtSource_smoothPrecoverage`: being locally of
  finite type is local on the source for the smooth topology.
* `AlgebraicGeometry.LocallyOfFinitePresentation.isLocalAtSource_smoothPrecoverage`: being
  locally of finite presentation is local on the source for the smooth topology.

## Implementation notes

Neither declaration carries a `@[stacks]` attribute. The Stacks statements that these are the
smooth cases of are **Stacks 036O** for local finite type and **Stacks 036N** for local finite
presentation, and both assert source locality for the *fppf* topology, which is strictly stronger
than the smooth statement proved here.

The smooth statement does *not* follow from the étale one: an étale covering is a smooth
covering and not conversely, so source locality for the smooth topology is the stronger assertion
and `CategoryTheory.MorphismProperty.IsLocalAtSource.of_le` runs the wrong way.

The two Zariski locality instances are supplied by name rather than by synthesis, because the
ring-homomorphism property indexing `AlgebraicGeometry.HasRingHomProperty` is not an output
parameter and so cannot be inferred from the morphism property alone. The
`CategoryTheory.MorphismProperty.RespectsLeft` instances are local.

## References

* [Stacks Project, Tag 02KK](https://stacks.math.columbia.edu/tag/02KK)
* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 036N](https://stacks.math.columbia.edu/tag/036N)
* [Stacks Project, Tag 036O](https://stacks.math.columbia.edu/tag/036O)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Being locally of finite type is local on the source for the smooth topology of schemes. -/
@[sga "3 V 9.1" "special case"]
instance LocallyOfFiniteType.isLocalAtSource_smoothPrecoverage :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Smooth.{u})) :=
  letI : MorphismProperty.RespectsLeft
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
    { precomp := fun i hi f hf => by
        have : Smooth i := hi
        have : LocallyOfFiniteType f := hf
        exact inferInstance }
  letI : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  letI : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  isLocalAtSource_smooth_of_affine_descent (@LocallyOfFiniteType.{u})
    fun {_X' _X _Y} _ _ _ g f hg hg' hcomp => by
      have : Surjective g := hg
      have : Smooth g := hg'
      have : LocallyOfFiniteType (g ≫ f) := hcomp
      rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
      refine RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation
        (f := f.appTop.hom) (g := g.appTop.hom) ?_ ?_
        (Scheme.Hom.finitePresentation_appTop g)
      · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
          HasRingHomProperty.appTop (@LocallyOfFiniteType.{u}) (g ≫ f) hcomp
      · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
          ⟨inferInstance, inferInstance⟩

/-- Being locally of finite presentation is local on the source for the smooth topology of
schemes. -/
@[sga "3 V 9.1" "special case", sga "3 VIB 10.8" "special case", sga "4 IV 8.5.5" "special case"]
instance LocallyOfFinitePresentation.isLocalAtSource_smoothPrecoverage :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (Scheme.precoverage (@Smooth.{u})) :=
  letI : MorphismProperty.RespectsLeft
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
    { precomp := fun i hi f hf => by
        have : Smooth i := hi
        have : LocallyOfFinitePresentation f := hf
        exact inferInstance }
  letI : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  letI : IsZariskiLocalAtTarget (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyOfFinitePresentation.{u}) (Q := RingHom.FinitePresentation)
  isLocalAtSource_smooth_of_affine_descent (@LocallyOfFinitePresentation.{u})
    fun {_X' _X _Y} _ _ _ g f hg hg' hcomp => by
      have : Surjective g := hg
      have : Smooth g := hg'
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
