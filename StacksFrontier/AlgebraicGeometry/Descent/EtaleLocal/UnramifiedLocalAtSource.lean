module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.FaithfullyFlatRing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.EtaleUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials

/-!
# Unramifiedness is local on the source for the étale topology (Stacks 04R3)

Unramifiedness of a morphism of schemes is local on the source for the étale topology: it may be
checked after an étale covering of the source, and it is inherited by the restriction of a
morphism to each member of such a covering. With the formal half of Tag 04R2 this gives the
unramified case of Tag 04R3: unramifiedness is étale local on the source and target.

The route is the étale case of Tag 036H,
`AlgebraicGeometry.isLocalAtSource_etale_of_affine_descent`, exactly as for local finite type and
for smoothness. Three of its four hypotheses are formal: unramifiedness is preserved by
precomposition with an étale morphism, because an étale morphism is unramified (Tag 03II) and
unramifiedness is stable under composition (Tag 02G9), and it is Zariski local on the source and
on the target through the `AlgebraicGeometry.HasRingHomProperty` instance recorded with the
characterizations of Tag 02G6.

The fourth hypothesis is descent along a surjective étale morphism `g : X' ⟶ X` of affine
schemes: if `g ≫ f` is unramified then so is `f`. By Tag 02G5 unramifiedness splits into local
finite type and the vanishing of the sheaf of relative differentials, and each half descends on
its own. Local finite type descends by Tag 0367,
`RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation`, whose two hypotheses on
`g` are what a surjective étale morphism of affines supplies: flat and surjective is faithfully
flat on global sections, and étale is of finite presentation. The vanishing of the relative
differentials descends by
`AlgebraicGeometry.isZero_relativeDifferentials_of_surjective_etale`, which is the conclusion the
source draws from the exact sequence of Tag 02K4 together with faithful flatness of `g`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Unramified.isLocalAtSource_etalePrecoverage`: unramifiedness is local on the
  source for the étale topology.
* `AlgebraicGeometry.Unramified.respectsRight_etale`: postcomposition with an étale morphism
  preserves unramifiedness.
* `AlgebraicGeometry.Unramified.isEtaleLocalOnSourceAndTarget`: **Stacks 04R3**, unramified case.
* `AlgebraicGeometry.unramified_isEtaleLocalOnSourceAndTarget`: the same statement under the
  unprefixed name, which is how the algebraic-space statements of Tags 0AML and 0AMM take it.

## Implementation notes

The three instances the Tag 036H criterion takes as instance arguments are supplied by `letI`
rather than by synthesis. For the two Zariski locality instances this is because the
ring-homomorphism property indexing `AlgebraicGeometry.HasRingHomProperty` is not an output
parameter, so it cannot be inferred from `AlgebraicGeometry.Unramified` alone. For
`CategoryTheory.MorphismProperty.RespectsLeft` it is to avoid a global instance whose only use is
here — the general fact that an étale-local-on-the-source property respects étale precomposition
is `AlgebraicGeometry.respectsLeft_etale_of_isLocalAtSource` (Tag 04QV), which becomes available
for unramifiedness as soon as this file's instance is.

Neither clause of Tag 03YV is recorded in this file: the unramified clause is
`AlgebraicGeometry.unramified_isLocalAtSource` and the G-unramified clause is
`AlgebraicGeometry.gUnramified_isLocalAtSource_etale`. The two clauses are independent statements
with independent proofs, the G-unramified one replacing Tag 0367 by Tag 02KK.

Tag 04R3 is a list of properties, one clause each, and only its unramified clause is proved
here. The geometric half of Tag 04R2 is not needed for it: postcomposition with an étale
morphism preserves unramifiedness outright, so
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource` applies directly, exactly
as for flatness, smoothness and local finite type.

## References

* [Stacks Project, Tag 02G5](https://stacks.math.columbia.edu/tag/02G5)
* [Stacks Project, Tag 02G6](https://stacks.math.columbia.edu/tag/02G6)
* [Stacks Project, Tag 02G9](https://stacks.math.columbia.edu/tag/02G9)
* [Stacks Project, Tag 02GA](https://stacks.math.columbia.edu/tag/02GA)
* [Stacks Project, Tag 02K4](https://stacks.math.columbia.edu/tag/02K4)
* [Stacks Project, Tag 02KK](https://stacks.math.columbia.edu/tag/02KK)
* [Stacks Project, Tag 0367](https://stacks.math.columbia.edu/tag/0367)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 03II](https://stacks.math.columbia.edu/tag/03II)
* [Stacks Project, Tag 03YV](https://stacks.math.columbia.edu/tag/03YV)
* [Stacks Project, Tag 04QV](https://stacks.math.columbia.edu/tag/04QV)
* [Stacks Project, Tag 04R2](https://stacks.math.columbia.edu/tag/04R2)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Unramifiedness descends along a surjective étale morphism of affine schemes: if `g : X' ⟶ X`
is surjective and étale, with `X'`, `X` and `Y` affine, and `g ≫ f` is unramified, then
`f : X ⟶ Y` is unramified.

Both halves of the characterization of Tag 02G5 descend: local finite type by Tag 0367, and the
vanishing of the sheaf of relative differentials by
`AlgebraicGeometry.isZero_relativeDifferentials_of_surjective_etale`. -/
theorem unramified_of_comp_surjective_etale_of_isAffine {X' X Y : Scheme.{u}}
    [IsAffine X'] [IsAffine X] [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    (hg : Surjective g) (hg' : Etale g) (hcomp : Unramified (g ≫ f)) : Unramified f := by
  have : Surjective g := hg
  have : Etale g := hg'
  obtain ⟨hcompFT, hcompΩ⟩ :=
    (unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials (g ≫ f)).mp hcomp
  refine (unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials f).mpr ⟨?_, ?_⟩
  · rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)]
    refine RingHom.finiteType_of_comp_of_faithfullyFlat_of_finitePresentation
      (f := f.appTop.hom) (g := g.appTop.hom) ?_ ?_
      (Scheme.Hom.finitePresentation_appTop g)
    · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
        HasRingHomProperty.appTop (@LocallyOfFiniteType.{u}) (g ≫ f) hcompFT
    · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
        ⟨inferInstance, inferInstance⟩
  · exact isZero_relativeDifferentials_of_surjective_etale f g hcompΩ

/-- Unramifiedness of morphisms of schemes is local on the source for the étale topology, in the
`AlgebraicGeometry.Scheme.etalePrecoverage` form.

This is the étale case of Tag 036H applied to unramifiedness. Its non-formal input is the descent
of unramifiedness along a surjective étale morphism of affine schemes.

The same statement is `AlgebraicGeometry.unramified_isLocalAtSource`, which is where the
unramified clause of Tag 03YV is recorded; this instance is kept because the étale-local
statement of Tag 04R3 below is built on it. -/
instance Unramified.isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource (@Unramified : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  letI : MorphismProperty.RespectsLeft (@Unramified.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    { precomp := fun i hi f hf =>
        have : Etale i := hi
        MorphismProperty.IsStableUnderComposition.comp_mem i f (unramified_of_etale i) hf }
  letI : IsZariskiLocalAtSource (@Unramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (Q := fun {_R _S : Type u} [CommRing _R] [CommRing _S] (φ : _R →+* _S) ↦
        φ.FormallyUnramified ∧ φ.FiniteType)
  letI : IsZariskiLocalAtTarget (@Unramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Unramified.{u})
      (Q := fun {_R _S : Type u} [CommRing _R] [CommRing _S] (φ : _R →+* _S) ↦
        φ.FormallyUnramified ∧ φ.FiniteType)
  isLocalAtSource_etale_of_affine_descent (@Unramified.{u})
    fun {_X' _X _Y} _ _ _ g f hg hg' hcomp =>
      unramified_of_comp_surjective_etale_of_isAffine g f hg hg' hcomp

/-- Postcomposition with an étale morphism preserves unramifiedness: an étale morphism is
unramified (Tag 03II), and unramified morphisms are stable under composition (Tag 02G9). -/
theorem Unramified.respectsRight_etale :
    MorphismProperty.RespectsRight (@Unramified : MorphismProperty Scheme.{u})
      (@Etale : MorphismProperty Scheme.{u}) where
  postcomp i hi f hf :=
    have : Etale i := hi
    MorphismProperty.IsStableUnderComposition.comp_mem f i hf (unramified_of_etale i)

/-- **Stacks Project, Tag 04R3, unramified case.** Being an unramified morphism of schemes is
étale local on the source and target.

This is the formal half of Tag 04R2 applied to unramifiedness: it is local on the source for the
étale topology by the instance above, stable under arbitrary base change by Tag 02GA, and
preserved by postcomposition with an étale morphism. -/
@[stacks 04R3 "unramified"]
theorem Unramified.isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (@Unramified : MorphismProperty Scheme.{u}) :=
  let := Unramified.respectsRight_etale.{u}
  IsEtaleLocalOnSourceAndTarget.of_isLocalAtSource _

/-- **Stacks Project, Tag 04R3, unramified case**, under the unprefixed name: being an unramified
morphism of schemes is étale local on the source and target.

This is `AlgebraicGeometry.Unramified.isEtaleLocalOnSourceAndTarget` spelled the way the
algebraic-space statements of Tag 0AML and Tag 0AMM, and the other properties in the Tag 04R3
list, name their instances of Tag 04QZ. -/
theorem unramified_isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (@Unramified.{u} : MorphismProperty Scheme.{u}) :=
  Unramified.isEtaleLocalOnSourceAndTarget.{u}

end AlgebraicGeometry

end
