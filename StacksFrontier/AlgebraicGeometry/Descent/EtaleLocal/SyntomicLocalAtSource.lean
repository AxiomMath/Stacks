module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothAlgebra
public import StacksFrontier.AlgebraicGeometry.Descent.SyntomicAlgebra
public import StacksFrontier.AlgebraicGeometry.Etale.Descent
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.RingHomProperty
public import StacksFrontier.RingTheory.CompleteIntersection.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Syntomic.Defs

/-!
# Syntomicity is local on the source for the étale topology (Stacks 04R3, syntomic case)

Syntomicity of morphisms of schemes is local on the source for the étale topology. This is the
syntomic case of Tag 02KM, and it is the one input the chain Tag 036H to Tag 04R3 to Tag 03MJ to
Tag 0AML and Tag 0AMM was missing for syntomicity; supplying it turns the conditional statements
about syntomic morphisms of algebraic spaces into their unconditional forms, Tags 03Z8 and 03Z9.

The instance is the étale case of Tag 036H,
`AlgebraicGeometry.isLocalAtSource_etale_of_affine_descent`, applied to
`AlgebraicGeometry.Syntomic`. Three of its four inputs are formal: syntomicity is preserved by
precomposition with an étale morphism, because an étale morphism is smooth and hence syntomic
(Tag 01VD) and syntomic morphisms compose (Tag 01UH); and syntomicity is Zariski local on the
source and on the target through `AlgebraicGeometry.HasRingHomProperty` at `RingHom.Syntomic`.

The fourth input is the mathematical content: syntomicity descends along a surjective étale
morphism of affine schemes. On rings this is the descent of `Algebra.Syntomic R ·` along a
faithfully flat algebra of finite presentation, and each of the three clauses of Definition 00SL
descends separately. Flatness over `R` descends by `Stacks.Etale.flat_of_flat_of_faithfullyFlat`
and finite presentation over `R` by
`Stacks.RingTheory.SmoothDescent.finitePresentation_of_faithfullyFlat` (Tag 02KK). What is left
is the fibre clause, that every fibre ring `κ(𝔭) ⊗_R A` is a local complete intersection over
`κ(𝔭)`: the fibres of a descent situation are again one, `κ(𝔭) ⊗_R B` being faithfully flat over
`κ(𝔭) ⊗_R A`, so this is the descent of the local complete intersection property over the field
`κ(𝔭)`. That whole argument is
`Stacks.RingTheory.SyntomicDescent.ringHom_syntomic_of_faithfullyFlat` in
`StacksFrontier.AlgebraicGeometry.Descent.SyntomicAlgebra`, which this file imports; it is not
reproved here.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Syntomic.respectsLeft_etale` and
  `AlgebraicGeometry.Syntomic.respectsRight_etale`: composing a syntomic morphism of schemes
  with an étale morphism on either side gives a syntomic morphism.
* `AlgebraicGeometry.syntomic_of_comp_surjective_syntomic_of_isAffine`: the syntomic case of
  Tag 02KM for affine schemes.
* `AlgebraicGeometry.Syntomic.isLocalAtSource_etalePrecoverage`: syntomicity of morphisms of
  schemes is local on the source for the étale topology.

## Implementation notes

The descent of the fibre clause is the direction of Tag 09Q2 that costs nothing. For a flat
local homomorphism of Noetherian local rings the completion of the target is a complete
intersection exactly when the completion of the source and the completion of the closed fibre
both are, and the clause wanted here is the first conjunct of that criterion, so no information
about the closed fibre of the étale local homomorphism is used at all. This is why the route
does not go through `AlgebraicGeometry.isCompleteIntersectionFibreAt_baseChange_iff` (Tag 02V3),
which an étale chart of the source cannot feed: such a chart is not a base change of the
morphism.

The affine descent is stated for affine schemes only, which is all the criterion of Tag 036H
asks for. Since an étale morphism is flat and locally of finite presentation, the surjectivity
and étaleness of `g` enter only as faithful flatness and finite presentation of `Γ(X) → Γ(X')`,
through `AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`.

The three instances the criterion of Tag 036H takes as instance arguments are supplied by `letI`
rather than by synthesis, exactly as in
`StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource`: the ring-homomorphism
property indexing `AlgebraicGeometry.HasRingHomProperty` is not an output parameter, so the two
Zariski locality instances cannot be inferred from `AlgebraicGeometry.Syntomic` alone.

## References

* [Stacks Project, Tag 00SL](https://stacks.math.columbia.edu/tag/00SL)
* [Stacks Project, Tag 01UH](https://stacks.math.columbia.edu/tag/01UH)
* [Stacks Project, Tag 01VD](https://stacks.math.columbia.edu/tag/01VD)
* [Stacks Project, Tag 02KK](https://stacks.math.columbia.edu/tag/02KK)
* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 09Q2](https://stacks.math.columbia.edu/tag/09Q2)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u

namespace AlgebraicGeometry

/-- Precomposition with an étale morphism preserves syntomicity of morphisms of schemes: an
étale morphism is syntomic and syntomic morphisms compose ([Stacks Project, Tag 01UH]). -/
theorem Syntomic.respectsLeft_etale :
    MorphismProperty.RespectsLeft (@Syntomic.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) where
  precomp i hi f hf :=
    have : Etale i := hi
    MorphismProperty.comp_mem _ i f (syntomic_of_etale i) hf

/-- Postcomposition with an étale morphism preserves syntomicity of morphisms of schemes: an
étale morphism is syntomic and syntomic morphisms compose ([Stacks Project, Tag 01UH]). -/
theorem Syntomic.respectsRight_etale :
    MorphismProperty.RespectsRight (@Syntomic.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) where
  postcomp i hi f hf :=
    have : Etale i := hi
    MorphismProperty.comp_mem _ f i hf (syntomic_of_etale i)

/-- **Stacks Project, Tag 02KM, syntomic case for affine schemes.** If `g` is a surjective
syntomic morphism of affine schemes and `g ≫ f` is syntomic, then `f` is syntomic.

A surjective syntomic morphism of affine schemes is flat and locally of finite presentation, so
on global sections `g` is a faithfully flat ring map of finite presentation and the statement is
`Stacks.RingTheory.SyntomicDescent.ringHom_syntomic_of_faithfullyFlat`. -/
theorem syntomic_of_comp_surjective_syntomic_of_isAffine {X' X Y : Scheme.{u}}
    [IsAffine X'] [IsAffine X] [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    (hgsurj : Surjective g) (hg : Syntomic g) (hcomp : Syntomic (g ≫ f)) : Syntomic f := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @Syntomic)]
  refine Stacks.RingTheory.SyntomicDescent.ringHom_syntomic_of_faithfullyFlat
    f.appTop.hom g.appTop.hom ?_
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨flat hg, hgsurj⟩)
    (HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) g
      (locallyOfFinitePresentation hg))
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
    HasRingHomProperty.appTop (P := @Syntomic) (g ≫ f) hcomp

/-- Syntomicity of morphisms of schemes is local on the source for the étale topology.

This is the étale case of Tag 036H applied to syntomicity. Its only non-formal input is the
syntomic case of Tag 02KM, the descent of syntomicity along a surjective étale morphism of
affine schemes. -/
instance Syntomic.isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource (@Syntomic : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  letI := Syntomic.respectsLeft_etale.{u}
  letI : IsZariskiLocalAtSource (@Syntomic.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Syntomic)
  letI : IsZariskiLocalAtTarget (@Syntomic.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Syntomic.{u}) (Q := RingHom.Syntomic)
  isLocalAtSource_etale_of_affine_descent (@Syntomic.{u}) fun g f hg hg' hcomp =>
    haveI : Etale g := hg'
    syntomic_of_comp_surjective_syntomic_of_isAffine g f hg (syntomic_of_etale g) hcomp

end AlgebraicGeometry

end
