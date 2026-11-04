module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange

/-!
# Smoothness is local on the source for the étale topology (Stacks 04R3, 03ZE)

Smoothness of morphisms of schemes is local on the source for the étale topology. This is the
one input that the chain Tag 036H to Tag 04R3 to Tag 03MJ to Tag 0AMM to Tag 03ZE was missing,
and supplying it turns the conditional statements of
`StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource` and
`StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange` into their unconditional forms.

The instance is the étale case of Tag 036H,
`AlgebraicGeometry.isLocalAtSource_etale_of_affine_descent`, applied to
`AlgebraicGeometry.Smooth`. That criterion asks for four things, and for smoothness the first
three are formal:

* smoothness is preserved by precomposition with an étale morphism, because an étale morphism
  is smooth and smooth morphisms compose;
* smoothness is Zariski local on the source and on the target, which is Mathlib's
  `AlgebraicGeometry.HasRingHomProperty` machinery for `RingHom.Smooth`.

The fourth is the only mathematical content: smoothness descends along a surjective étale
morphism of affine schemes. That is the smooth case of Tag 02KM, which is already available as
`Stacks.Smooth.smooth_of_comp_surjective_smooth` — an étale morphism is smooth, so the affine
hypotheses are not even used.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Smooth.isLocalAtSource_etalePrecoverage`: smoothness of morphisms of
  schemes is local on the source for the étale topology.
* `AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget`: **Stacks 04R3**, smooth case,
  unconditionally.
* `AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange`: **Stacks 03ZE**, smoothness of
  morphisms of algebraic spaces is stable under base change, unconditionally.

## Implementation notes

The three instances the Tag 036H criterion takes as instance arguments are supplied by `letI`
rather than by synthesis. For the two Zariski locality instances this is because the
ring-homomorphism property indexing `AlgebraicGeometry.HasRingHomProperty` is not an output
parameter, so it cannot be inferred from `AlgebraicGeometry.Smooth` alone; the same two terms
appear by name in Mathlib's own `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`. For
`CategoryTheory.MorphismProperty.RespectsLeft` it is to avoid a global instance whose only use
is here — the general fact that an étale-local-on-the-source property respects étale
precomposition is `AlgebraicGeometry.respectsLeft_etale_of_isLocalAtSource` (Tag 04QV), which
is available for smoothness as soon as this file's instance is.

`AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget` and
`AlgebraicGeometry.Space.isSmooth_isStableUnderBaseChange` carry the tags `04R3` and `03ZE`
because they are the first unconditional forms of those statements. The versions in
`FromLocalAtSource` and `EtaleChartBaseChange` are deliberately untagged there: each takes the
étale source-locality of smoothness as a hypothesis, and an instance argument is still a
hypothesis.

## References

* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 04QV](https://stacks.math.columbia.edu/tag/04QV)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Smoothness of morphisms of schemes is local on the source for the étale topology.

This is the étale case of Tag 036H applied to smoothness. Its only non-formal input is the
smooth case of Tag 02KM, the descent of smoothness along a surjective étale morphism. -/
@[sga "1 II 1.3" "(iii), special case"]
instance Smooth.isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource (@Smooth : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  letI : MorphismProperty.RespectsLeft (@Smooth.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    { precomp := fun i hi f hf => by
        have : Etale i := hi
        have : Smooth f := hf
        exact inferInstance }
  letI : IsZariskiLocalAtSource (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  letI : IsZariskiLocalAtTarget (@Smooth.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth.{u}) (Q := RingHom.Smooth)
  isLocalAtSource_etale_of_affine_descent (@Smooth.{u}) fun g f hg hg' hcomp =>
    have : Surjective g := hg
    have : Etale g := hg'
    have : Smooth (g ≫ f) := hcomp
    Stacks.Smooth.smooth_of_comp_surjective_smooth g f

/-- **Stacks Project, Tag 04R3, smooth case.** Being a smooth morphism of schemes is étale
local on the source and target. -/
@[stacks 04R3 "smooth", sga "1 II 1.3" "special case"]
theorem Smooth.isEtaleLocalOnSourceAndTarget :
    IsEtaleLocalOnSourceAndTarget (@Smooth : MorphismProperty Scheme.{u}) :=
  smooth_isEtaleLocalOnSourceAndTarget

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks Project, Tag 03ZE.** Smoothness of morphisms of algebraic spaces over `S` is
stable under base change. -/
@[stacks 03ZE, sga "1 II 1.3" "(ii)"]
theorem isSmooth_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (fun ⦃F G : AlgebraicSpaces B S hS⦄ (f : F ⟶ G) => IsSmooth B S hS f.hom) :=
  isSmooth_isStableUnderBaseChange_of_isEtaleLocal B S hS Smooth.isEtaleLocalOnSourceAndTarget

end Space

end AlgebraicGeometry

end
