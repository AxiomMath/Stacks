module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Smooth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smooth, étale and unramified representable transformations (Stacks 04AL)

Let `S` be a scheme, let `F, G : (Sch/S)_{fppf}^{opp} ⥤ Set`, and let `a : F ⟶ G` be a
representable transformation of functors.  Stacks 04AL draws three conclusions at once: if `a`
is smooth it is formally smooth, if `a` is étale it is formally étale, and if `a` is unramified
it is formally unramified.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.formallySmooth_formallyEtale_formallyUnramified_of_representable`:
  **Stacks 04AL**, the whole lemma — all three implications for one representable
  transformation.

## Implementation notes

The three implications are the separately proved parts
`AlgebraicGeometry.Space.formallySmooth_of_smooth`,
`AlgebraicGeometry.Space.formallyEtale_of_etale` and
`AlgebraicGeometry.Space.formallyUnramified_of_unramified`, and this module only states them
together under the source's shared hypotheses, so that one declaration says the whole tag.
Each part keeps its own part string; the bare attribute sits here.

The source's standing hypothesis that `a` is a representable transformation of functors is not
a separate binder.  In this library the smoothness, étaleness and unramifiedness of a
transformation are spelled by `CategoryTheory.MorphismProperty.presheaf`, which *bundles*
relative representability with the requirement that every represented base change have the
property of schemes in question — `ha.1` of each antecedent below is exactly
`CategoryTheory.Functor.relativelyRepresentable a`.  So representability is a hypothesis of
every one of the three implications, as the source has it, and a fourth binder asserting it
again would be redundant.

## References

* [Stacks Project, Tag 04AL](https://stacks.math.columbia.edu/tag/04AL)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 04AL.**  Let `S` be a scheme, let `F` and `G` be set-valued functors on the big
fppf site over `S`, and let `a : F ⟶ G` be a representable transformation of functors.  Then

1. if `a` is smooth it is formally smooth;
2. if `a` is étale it is formally étale;
3. if `a` is unramified it is formally unramified.

Each part is proved by turning the lifting problem into one for the scheme representing the
base change of `a` along a point of the target, where the corresponding implication for
morphisms of schemes applies; see
`AlgebraicGeometry.Space.formallySmooth_of_smooth`,
`AlgebraicGeometry.Space.formallyEtale_of_etale` and
`AlgebraicGeometry.Space.formallyUnramified_of_unramified`, which this statement assembles. -/
@[stacks 04AL, ega "0 19.0.1" "partial", sga "3 XI 1.6" "necessity direction"]
public theorem formallySmooth_formallyEtale_formallyUnramified_of_representable
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    ((MorphismProperty.inverseImage (@Smooth.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a → FormallySmooth a) ∧
      ((MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a → FormallyEtale a) ∧
      ((MorphismProperty.inverseImage (@Unramified.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a → FormallyUnramified a) :=
  ⟨formallySmooth_of_smooth B S hS a, formallyEtale_of_etale B S hS a,
    formallyUnramified_of_unramified B S hS a⟩

end AlgebraicGeometry.Space

end
