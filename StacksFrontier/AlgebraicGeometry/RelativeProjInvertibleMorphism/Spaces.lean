module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProj

/-!
# The morphism of algebraic spaces into relative Proj classified by an invertible quotient

[Stacks, Tag 0D2Z] attaches to a graded quasi-coherent `𝒪_Y`-algebra `𝒜` on an algebraic
space `Y`, a morphism of algebraic spaces `f : X ⟶ Y`, an invertible `𝒪_X`-module `ℒ` and a
graded algebra map `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}` a canonical morphism of algebraic spaces
over `Y`

  `r_{ℒ,ψ} : U(ψ) ⟶ Proj_Y(𝒜)`

characterized by three properties, of which (2) is the one that pins the morphism down: *for
`d ≥ 1` and a scheme `W ⟶ X` on which `ψ` is surjective in degree `d`, the morphism
`W ⟶ Proj_Y(𝒜)` obtained by composing with `r_{ℒ,ψ}` is the one the construction of relative
Proj attaches to the quadruple `(d, W ⟶ Y, ℒ|_W, ψ^{(d)}|_W)`.*  The source's own proof builds
`r_{ℒ,ψ}` out of exactly those morphisms: they are a transformation of functors on
`(Sch/S)_{fppf}`, and that transformation is the morphism.

This file supplies those morphisms, for the relative Proj of an algebraic space as
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProj.lean` presents it: through its base changes
to schemes, which is the second assertion of [Stacks, Tag 084B] and all that the proof of
[Stacks, Tag 085D] uses.  Given a scheme object `T` of the site, a `T`-point `x` of `Y` and a
pair `(ℒ, ψ)` on a scheme over `T`, with `ψ` surjective in degree one, we obtain a morphism of
algebraic spaces from that scheme into `Proj_Y(𝒜)` lying over `x`, and that morphism is
compatible with further base change of the test scheme.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjPoints.pointOfPair` is the morphism of algebraic spaces
  into `Proj_Y(𝒜)` classified by a pair over a scheme point of the base: the morphism
  `W ⟶ Proj_Y(𝒜)` of characterizing property (2) of Tag 0D2Z.

## Main results

* `AlgebraicGeometry.Space.RelativeProjPoints.pointOfPair_comp_toBase`: it lies over the point
  of the base it was built on, so it is a morphism *over* `Y`.
* `AlgebraicGeometry.Space.RelativeProjPoints.pointOfPair_spec`: the class of triples it induces
  is the class of the pair it was built from.  With
  `AlgebraicGeometry.Space.RelativeProjPoints.eq_pointOfPair_iff` this is the uniqueness that
  makes it *the* canonical morphism rather than a choice: it is the only morphism over `x`
  inducing that class.
* `AlgebraicGeometry.Space.RelativeProjPoints.map_comp_pointOfPair`: **characterizing property
  (2) under base change.**  Restricting the morphism along `r' : T'' ⟶ T'` gives the morphism
  classified by the pulled-back pair.  This is what makes the family of morphisms of property (2)
  a transformation of functors, which is the step the source's proof takes to produce
  `r_{ℒ,ψ}`.

## Implementation notes

**No tag is claimed.**  What Tag 0D2Z asserts, and this file does not, is that the morphisms
below assemble into a morphism out of an *open subspace* `U(ψ)` of `X`: that needs `U(ψ)` itself,
hence a graded map that is not assumed surjective and the openness of its surjectivity locus,
neither of which this library has — see the implementation notes of
`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/Basic.lean`.  It also needs the
descent of the family to an algebraic space `X`, which for this presentation of the relative Proj
would need the algebras `d.algebra T f` at different points of the base to be compared, and
`AlgebraicGeometry.Space.RelativeProjPoints` carries no such comparison.  The graded-algebra map
`θ` and clause (1) of the tag are likewise absent.

**Hypotheses.**  The hypotheses are exactly those of Tag 085D in this library: the
tensor algebras `TA` and their pullback comparisons `i` as data, degree-one generation `hgen` of
the restricted algebras, and the scheme-level representing bijections `rep` of [Stacks,
Tag 01O4].  Degree one rather than an arbitrary `d ≥ 1` is the restriction `F1Pair` imposes; see
the implementation notes of the `Basic` file.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 085D](https://stacks.math.columbia.edu/tag/085D)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjRepresentsF1
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace AlgebraicGeometry.Space

universe u

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Y Proj : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : Proj ⟶ Y}
    (d : RelativeProjPoints B S hS π)
    (TA : TensorAlgebras.{u}) (i : TensorAlgebraPullbackIsos.{u} TA)
    {D : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ Y),
      TwistData (d.algebra T f)}
    (hgen : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ Y),
      IsGeneratedInDegreeOne (d.algebra T f))
    (rep : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ Y),
      F1Representation (d.algebra T f) TA i (D T f))

/-- **The morphism `W ⟶ Proj_Y(𝒜)` of characterizing property (2) of Tag 0D2Z.**

Let `x` be a `T`-point of the base `Y` and let `r : T' ⟶ T` present a scheme over `T`.  An
invertible module on the scheme of `T'` together with a graded algebra map out of the restricted
algebra `x^*𝒜`, surjective in degree one, classifies a morphism of algebraic spaces
`T' ⟶ Proj_Y(𝒜)` lying over `x ∘ r`.

This is the morphism the source's proof attaches to a quadruple `(d, W ⟶ Y, ℒ|_W, ψ^{(d)}|_W)`,
read through the representation of the relative Proj by the functor of triples, Tag 085D. -/
public def pointOfPair (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ Y)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (P : F1Pair (d.algebra T x) TA ((BigFppfOver.toScheme B S hS).map r)) :
    yoneda.obj T' ⟶ Proj :=
  ((d.pointEquivF1 TA i hgen rep T x r).symm (Quot.mk _ P)).1

/-- **The classifying morphism lies over the point of the base.**  This is the assertion of
Tag 0D2Z that `r_{ℒ,ψ}` is a morphism of algebraic spaces *over* `Y`. -/
public theorem pointOfPair_comp_toBase (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ Y)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (P : F1Pair (d.algebra T x) TA ((BigFppfOver.toScheme B S hS).map r)) :
    d.pointOfPair TA i hgen rep T x r P ≫ π = yoneda.map r ≫ x :=
  ((d.pointEquivF1 TA i hgen rep T x r).symm (Quot.mk _ P)).2

/-- **The classifying morphism induces the class of the pair it was built from.** -/
public theorem pointOfPair_spec (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ Y)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (P : F1Pair (d.algebra T x) TA ((BigFppfOver.toScheme B S hS).map r)) :
    d.pointEquivF1 TA i hgen rep T x r
        ⟨d.pointOfPair TA i hgen rep T x r P,
          d.pointOfPair_comp_toBase TA i hgen rep T x r P⟩ = Quot.mk _ P :=
  (d.pointEquivF1 TA i hgen rep T x r).apply_symm_apply _

/-- **The classifying morphism is the only morphism over the point inducing that class.**  This
is the "characterized by" of Tag 0D2Z for a scheme test object: `pointOfPair` is canonical, not a
choice. -/
public theorem eq_pointOfPair_iff (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ Y)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T)
    (P : F1Pair (d.algebra T x) TA ((BigFppfOver.toScheme B S hS).map r))
    (u : {u : yoneda.obj T' ⟶ Proj // u ≫ π = yoneda.map r ≫ x}) :
    u.1 = d.pointOfPair TA i hgen rep T x r P ↔
      d.pointEquivF1 TA i hgen rep T x r u = Quot.mk _ P := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [show u = ⟨d.pointOfPair TA i hgen rep T x r P,
      d.pointOfPair_comp_toBase TA i hgen rep T x r P⟩ from Subtype.ext h]
    exact d.pointOfPair_spec TA i hgen rep T x r P
  · exact congrArg Subtype.val ((Equiv.eq_symm_apply _).mpr h)

/-- **Characterizing property (2) under base change.**  Restricting the classifying morphism
along `r' : T'' ⟶ T'` yields the morphism classified by the pulled-back pair.  It is this
compatibility that makes the morphisms of property (2) a transformation of functors, out of which
the source's proof produces `r_{ℒ,ψ}`. -/
public theorem map_comp_pointOfPair (T : BigFppfOver B S hS) (x : yoneda.obj T ⟶ Y)
    {T' T'' : BigFppfOver B S hS} (r : T' ⟶ T) (r' : T'' ⟶ T')
    (P : F1Pair (d.algebra T x) TA ((BigFppfOver.toScheme B S hS).map r))
    (Q : F1Pair (d.algebra T x) TA ((BigFppfOver.toScheme B S hS).map r' ≫
      (BigFppfOver.toScheme B S hS).map r))
    (hQ : IsPullbackPair (d.algebra T x) TA i ((BigFppfOver.toScheme B S hS).map r') P Q) :
    yoneda.map r' ≫ d.pointOfPair TA i hgen rep T x r P =
      d.pointOfPair TA i hgen rep T x (r' ≫ r) Q := by
  refine ((d.eq_pointOfPair_iff TA i hgen rep T x (r' ≫ r) Q
    ⟨yoneda.map r' ≫ d.pointOfPair TA i hgen rep T x r P, ?_⟩).mpr ?_)
  · rw [Category.assoc, d.pointOfPair_comp_toBase TA i hgen rep T x r P, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp]
  · rw [d.pointEquivF1_natural TA i hgen rep T x r r'
      ⟨d.pointOfPair TA i hgen rep T x r P,
        d.pointOfPair_comp_toBase TA i hgen rep T x r P⟩,
      d.pointOfPair_spec TA i hgen rep T x r P]
    exact pullbackClass_quot_mk (d.algebra T x) TA (rep T x)
      ((BigFppfOver.toScheme B S hS).map r') P Q hQ

end RelativeProjPoints

end AlgebraicGeometry.Space

end
