module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SyntomicDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FactorSyntomic
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Charts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic

/-!
# Syntomicity of the factors of a syntomic morphism of algebraic spaces

Let `X ⟶ Y ⟶ Z` be morphisms of algebraic spaces over a scheme `S`, with `f : X ⟶ Y` surjective,
flat and locally of finite presentation. If the composite `f ≫ q` is syntomic then both factors
are syntomic. Syntomicity of `f` does not use surjectivity.

## Main results

* `AlgebraicGeometry.Space.isSyntomic_of_comp_of_fppf`: **Stacks 0AHF**, syntomicity of the
  second factor.
* `AlgebraicGeometry.Space.isSyntomic_of_isSyntomic_comp_of_fppf`: **Stacks 0AHF**, syntomicity
  of the first factor.

## Implementation notes

The source's morphism `X ⟶ Z` is expressed as the composite `f ≫ q`, and the source's two
conclusions are stated separately so that the second one carries no surjectivity hypothesis.

Syntomicity of a morphism of algebraic spaces is the every-chart condition of Tag 03MJ, so both
statements reduce to the corresponding statements about morphisms of schemes. A surjective étale
atlas `c` of `Z` is lifted through `q` and then through `f` by
`AlgebraicGeometry.Space.exists_etale_chart_square_over`, which produces compatible surjective
étale charts `a` of `X`, `b` of `Y` and `c` of `Z` together with morphisms `h` and `k` of the
site, and makes `h` surjective as a morphism of schemes as soon as `f` is surjective on points.
The underlying morphism `h` of schemes is flat and locally of finite presentation because `f` is,
and `h ≫ k` is syntomic because `f ≫ q` is; so Tag 05B7 applies to the pair `(h, k)` — its
conclusion about the first factor in the form `syntomic_of_syntomic_comp_of_flat`, which needs no
surjectivity, and its conclusion about the second factor as
`Stacks.Syntomic.syntomic_of_comp_of_fppf`. One surjective chart square suffices by Tag 03MJ,
which is available for syntomicity because being syntomic is étale local on the source and target
(Tag 04R3).

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03Z7](https://stacks.math.columbia.edu/tag/03Z7)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 05B7](https://stacks.math.columbia.edu/tag/05B7)
* [Stacks Project, Tag 0AHF](https://stacks.math.columbia.edu/tag/0AHF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Both conclusions of **Stacks 0AHF** at once: if `f : X ⟶ Y` is a flat morphism of algebraic
spaces over `S` which is locally of finite presentation and `f ≫ q` is syntomic, then `f` is
syntomic, and so is `q` as soon as `f` is surjective. -/
private theorem isSyntomic_factors_of_isSyntomic_comp
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (q : Y ⟶ Z)
    (hff : IsFlat B S hS f) (hflfp : IsLocallyOfFinitePresentation B S hS f)
    (hp : IsSyntomic B S hS (f ≫ q)) :
    IsSyntomic B S hS f ∧ (IsSurjective B S hS f → IsSyntomic B S hS q) := by
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨W, c, hcS, hcE⟩ := hZ.exists_atlas
  obtain ⟨V, b, k, hbE, hk, hbSof, -⟩ :=
    exists_etale_chart_square_over B S hS hY hZ q W c hcE
  have hbS := hbSof hcS
  obtain ⟨U, a, h, haE, hh, haSof, hs⟩ :=
    exists_etale_chart_square_over B S hS hX hY f V b hbE
  have haS := haSof hbS
  have : _root_.AlgebraicGeometry.Flat (T.map h) := hff U V a b h haE hbE hh
  have : _root_.AlgebraicGeometry.LocallyOfFinitePresentation (T.map h) :=
    hflfp U V a b h haE hbE hh
  have hp' : _root_.AlgebraicGeometry.Syntomic (T.map h ≫ T.map k) := by
    rw [← T.map_comp]
    apply hp U W a c (h ≫ k) haE hcE
    rw [Functor.map_comp, Category.assoc, hk, ← Category.assoc, hh, Category.assoc]
  refine ⟨?_, fun hfs ↦ ?_⟩
  · exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _
      _root_.AlgebraicGeometry.syntomic_isEtaleLocalOnSourceAndTarget hX hY f).mpr
      ⟨U, V, a, b, h, haE, hbE, haS, hh,
        _root_.AlgebraicGeometry.syntomic_of_syntomic_comp_of_flat (T.map h) (T.map k) hp'⟩
  · have : _root_.AlgebraicGeometry.Surjective (T.map h) := hs hfs
    exact (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _
      _root_.AlgebraicGeometry.syntomic_isEtaleLocalOnSourceAndTarget hY hZ q).mpr
      ⟨V, W, b, c, k, hbE, hcE, hbS, hk,
        Stacks.Syntomic.syntomic_of_comp_of_fppf (T.map h) (T.map k) hp'⟩

/-- **Stacks 0AHF.** Syntomicity descends from a composite of morphisms of algebraic spaces over
`S` along a surjective, flat morphism which is locally of finite presentation: if `f : X ⟶ Y` is
surjective, flat and locally of finite presentation and `f ≫ q` is syntomic, then `q : Y ⟶ Z` is
syntomic. -/
@[stacks 0AHF "syntomicity of q"]
theorem isSyntomic_of_comp_of_fppf
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (q : Y ⟶ Z)
    (hfs : IsSurjective B S hS f) (hff : IsFlat B S hS f)
    (hflfp : IsLocallyOfFinitePresentation B S hS f)
    (hp : IsSyntomic B S hS (f ≫ q)) :
    IsSyntomic B S hS q :=
  (isSyntomic_factors_of_isSyntomic_comp B S hS hX hY hZ f q hff hflfp hp).2 hfs

/-- **Stacks 0AHF.** A flat morphism of algebraic spaces over `S` which is locally of finite
presentation is syntomic as soon as its composite with another morphism is syntomic. The source
states this alongside the conclusion about the other factor, under the extra hypothesis that `f`
be surjective; surjectivity is not needed here. -/
@[stacks 0AHF "syntomicity of f"]
theorem isSyntomic_of_isSyntomic_comp_of_fppf
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (q : Y ⟶ Z)
    (hff : IsFlat B S hS f) (hflfp : IsLocallyOfFinitePresentation B S hS f)
    (hp : IsSyntomic B S hS (f ≫ q)) :
    IsSyntomic B S hS f :=
  (isSyntomic_factors_of_isSyntomic_comp B S hS hX hY hZ f q hff hflfp hp).1

end AlgebraicGeometry.Space

end
