module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality

/-!
# Local finite type is local on the source for the étale topology (Stacks 04R3)

Being locally of finite type is local on the source for the étale topology, hence, by the formal
half of Tag 04R2, étale local on the source and target. This is the case of Tag 04R3 listed there
as "locally finite type", and it is the input the Tag 0AML and Tag 0AMM statements for algebraic
spaces take for local finite type.

The route is the étale case of Tag 036H,
`AlgebraicGeometry.isLocalAtSource_etale_of_affine_descent`, exactly as for local finite
presentation. Three of its four hypotheses are formal: being locally of finite type is preserved
by precomposition with an étale morphism, because an étale morphism is locally of finite type and
the property is stable under composition, and it is Zariski local on the source and on the target
through Mathlib's `AlgebraicGeometry.HasRingHomProperty` machinery for `RingHom.FiniteType`.

The fourth hypothesis is descent along a surjective étale morphism of affine schemes. On global
sections it reads: for ring maps `R → A → B` with `R → B` of finite type and `A → B` faithfully
flat and of finite presentation, `R → A` is of finite type. That is Tag 0367,
`RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation`. Its two hypotheses on
`A → B` are exactly what a surjective étale morphism of affines gives: flat and surjective is
faithfully flat on global sections, and étale is of finite presentation.

Also proved here is the cancellation property of Tag 01T8, which the corresponding statement for
algebraic spaces (Tag 0462) reduces to on charts: it is Mathlib's
`AlgebraicGeometry.HasRingHomProperty.of_comp` fed with the observation that a ring map whose
composite with a map into it is of finite type is itself of finite type, generators over the
smaller ring being generators over the larger one.

## Main definitions

There are no new definitions.

## Main results

* `RingHom.finiteType_of_finiteType_comp`: if `R → A → B` has `R → B` of finite type, then
  `A → B` is of finite type.
* `AlgebraicGeometry.LocallyOfFiniteType.of_comp`: **Stacks 01T8**.
* `AlgebraicGeometry.LocallyOfFiniteType.isLocalAtSource_etalePrecoverage`: being locally of
  finite type is local on the source for the étale topology.
* `AlgebraicGeometry.LocallyOfFiniteType.respectsRight_etale`: postcomposition with an étale
  morphism preserves local finite type.
* `AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget`: **Stacks 04R3**, the
  case of being locally of finite type.

## Implementation notes

`AlgebraicGeometry.LocallyOfFiniteType.isLocalAtSource_etalePrecoverage` is deliberately **not**
tagged `@[stacks 036O]`: Tag 036O asserts that local finite type is fppf local on the source,
which is strictly stronger than the étale statement proved here. The same choice was made for
local finite presentation and Tag 036N.

The two Zariski locality instances are supplied by name rather than by synthesis, because the
ring-homomorphism property indexing `AlgebraicGeometry.HasRingHomProperty` is not an output
parameter and so cannot be inferred from `AlgebraicGeometry.LocallyOfFiniteType` alone. The
`CategoryTheory.MorphismProperty.RespectsLeft` instance is local for the same reason: the general
statement that an étale-local-on-the-source property respects étale precomposition is
`AlgebraicGeometry.respectsLeft_etale_of_isLocalAtSource` (Tag 04QV), which becomes available for
this property only once the instance below is.

`AlgebraicGeometry.LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget` carries the tag because it
is unconditional; every instance argument is discharged here, and an instance argument is still a
hypothesis.

## References

* [Stacks Project, Tag 01T8](https://stacks.math.columbia.edu/tag/01T8)
* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 036O](https://stacks.math.columbia.edu/tag/036O)
* [Stacks Project, Tag 04QV](https://stacks.math.columbia.edu/tag/04QV)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace RingHom

/-- If the composite of `f : R →+* A` with `g : A →+* B` is of finite type, then `g` is of finite
type: a finite set of generators of `B` as an `R`-algebra generates it as an `A`-algebra. -/
theorem finiteType_of_finiteType_comp {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (h : (g.comp f).FiniteType) : g.FiniteType := by
  algebraize [f, g, g.comp f]
  exact Algebra.FiniteType.of_restrictScalars_finiteType R A B

end RingHom

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 01T8.** If a composite of morphisms of schemes is locally of finite
type, then so is its first factor. -/
@[stacks 01T8, ega "IV 1.3.4"]
theorem LocallyOfFiniteType.of_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (h : LocallyOfFiniteType (f ≫ g)) : LocallyOfFiniteType f :=
  HasRingHomProperty.of_comp (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
    (fun f g hfg => RingHom.finiteType_of_finiteType_comp f g hfg) h

/-- Being locally of finite type is local on the source for the étale topology.

This is the étale case of Tag 036H applied to local finite type. Its only non-formal input is
Tag 0367, the descent of finite type along a faithfully flat ring map of finite presentation. -/
instance LocallyOfFiniteType.isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) Scheme.etalePrecoverage :=
  letI : MorphismProperty.RespectsLeft
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    { precomp := fun i hi f hf => by
        have : Etale i := hi
        have : LocallyOfFiniteType f := hf
        exact inferInstance }
  letI : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  letI : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  isLocalAtSource_etale_of_affine_descent (@LocallyOfFiniteType.{u})
    fun {_X' _X _Y} _ _ _ g f hg hg' hcomp => by
      have : Surjective g := hg
      have : Etale g := hg'
      have : LocallyOfFiniteType (g ≫ f) := hcomp
      rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
      refine RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation
        (f := f.appTop.hom) (g := g.appTop.hom) ?_ ?_
        (Scheme.Hom.finitePresentation_appTop g)
      · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
          HasRingHomProperty.appTop (@LocallyOfFiniteType.{u}) (g ≫ f) hcomp
      · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
          ⟨inferInstance, inferInstance⟩

/-- Postcomposition with an étale morphism preserves local finite type: an étale morphism is
locally of finite type, and the property is stable under composition. -/
@[ega "IV 1.3.4" "(ii), special case"]
theorem LocallyOfFiniteType.respectsRight_etale :
    MorphismProperty.RespectsRight
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) where
  postcomp i hi f hf := by
    have : Etale i := hi
    have : LocallyOfFiniteType f := hf
    exact inferInstance

/-- **Stacks Project, Tag 04R3, the case of being locally of finite type.** Being a morphism of
schemes locally of finite type is étale local on the source and target. -/
@[stacks 04R3 "locally finite type"]
theorem LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
  let := LocallyOfFiniteType.respectsRight_etale.{u}
  IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource _

end AlgebraicGeometry

end
