module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion

/-!
# Descent of sections along a one-morphism fppf covering

A surjective flat morphism locally of finite presentation of the big fppf category over `S`
generates a covering sieve, so a sheaf on the big fppf site is a sheaf for the one-element
family it spans. In equalizer form: for such a morphism `f : V ⟶ U` completed to a cartesian
square by `p₁, p₂ : W ⟶ V`, the sections over `U` are the equalizer of the two restrictions
`F(V) ⇉ F(W)`.

This is the shape in which descent is applied to a single faithfully flat ring extension
`R ⟶ R'`, with `W = Spec (R' ⊗_R R')`.

## Main results

* `AlgebraicGeometry.BigFppfOver.bijective_mapToEqualizer_of_isSheaf_of_flat`: the equalizer
  form for a surjective flat morphism locally of finite presentation.
* `AlgebraicGeometry.BigFppfOver.bijective_mapToEqualizer_of_isSheaf_of_etale`: the same for a
  surjective étale morphism.

## References

* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.BigFppfOver

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type w)

/-- A sheaf on the big fppf site over `S` is a sheaf for the one-element family spanned by a
surjective flat morphism locally of finite presentation. -/
theorem isSheafFor_singleton_of_isSheaf_of_flat
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {V U : BigFppfOver B S hS} (f : V ⟶ U)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map f))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f)) :
    Presieve.IsSheafFor F (Presieve.singleton f) :=
  (Presieve.isSheafFor_iff_generate (Presieve.singleton f)).2
    ((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) F).1 hF _
      (Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS f hsurj hflat hlfp))

/-- **The sections of a sheaf on the big fppf site over `S` are the equalizer of the two
restrictions along a one-morphism covering.** For `f : V ⟶ U` surjective, flat and locally of
finite presentation, and `p₁, p₂ : W ⟶ V` completing `f` to a cartesian square, so that
`W = V ×_U V`, a sheaf `F` maps `F(U)` bijectively onto the equalizer of `F(V) ⇉ F(W)`. -/
theorem bijective_mapToEqualizer_of_isSheaf_of_flat
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {V U W : BigFppfOver B S hS} (f : V ⟶ U) (p₁ p₂ : W ⟶ V)
    (hW : IsPullback p₁ p₂ f f)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (hflat : Flat ((BigFppfOver.toScheme B S hS).map f))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map f)) :
    Function.Bijective (regularTopology.mapToEqualizer F f p₁ p₂ hW.w) :=
  (isSheafFor_singleton_iff_bijective_mapToEqualizer f p₁ p₂ hW).1
    (isSheafFor_singleton_of_isSheaf_of_flat B S hS F hF f hsurj hflat hlfp)

/-- The equalizer form of the sheaf condition for the one-element family spanned by a
surjective étale morphism of the big fppf category over `S`. -/
theorem bijective_mapToEqualizer_of_isSheaf_of_etale
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {V U W : BigFppfOver B S hS} (f : V ⟶ U) (p₁ p₂ : W ⟶ V)
    (hW : IsPullback p₁ p₂ f f)
    (hsurj : Surjective ((BigFppfOver.toScheme B S hS).map f))
    (hetale : Etale ((BigFppfOver.toScheme B S hS).map f)) :
    Function.Bijective (regularTopology.mapToEqualizer F f p₁ p₂ hW.w) :=
  (isSheafFor_singleton_iff_bijective_mapToEqualizer f p₁ p₂ hW).1
    (isSheafFor_singleton_of_isSheaf_of_flat B S hS F hF f hsurj inferInstance inferInstance)

end AlgebraicGeometry.BigFppfOver

end
