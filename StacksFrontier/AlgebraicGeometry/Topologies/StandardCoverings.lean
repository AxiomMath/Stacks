module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs

/-!
# Coverings for the five standard topologies on schemes

Five topologies on schemes — fppf, syntomic, smooth, étale and Zariski — are defined by the
same recipe: a family of morphisms `fᵢ : Uᵢ ⟶ T` with a fixed target is a covering when every
`fᵢ` has the property of morphisms belonging to the topology and the images of the `fᵢ` cover
`T`. Such a covering is *standard* when, in addition, the index type is finite, the target and
every source is affine, and every member has the standard affine form attached to the
topology: a relative global complete intersection in the syntomic case, a standard smooth ring
map in the smooth case, and a basic open immersion in the Zariski case.

## Main definitions

* `AlgebraicGeometry.CoveringTopology` lists the five topologies.
* `AlgebraicGeometry.coveringMorphismProperty` selects the required property of the members of
  a covering family for each topology.
* `AlgebraicGeometry.IsStandardCovering` is the predicate singling out the standard coverings
  of an affine scheme.

## Main results

* `AlgebraicGeometry.Scheme.precoverage` is the precoverage whose coverings are the
  `τ`-coverings, and `AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff` characterizes them
  by joint surjectivity together with the componentwise property.

## Implementation notes

A `τ`-covering is not given a predicate of its own: Mathlib's
`AlgebraicGeometry.Scheme.precoverage` already takes a property of morphisms of schemes to the
precoverage of jointly surjective families with that property, so a `τ`-covering with target
`T` is exactly a presieve on `T` belonging to `Scheme.precoverage (coveringMorphismProperty τ)`.
In the fppf case the morphism property is flatness together with local finite presentation.

Standard coverings, by contrast, are not of this shape, since their definition constrains the
sources and the index type as well as the individual morphisms; they are a structure, so that
a client may name its clauses. The index type is an arbitrary finite type rather than a chosen
`Fin m`, and the family of morphisms is retained rather than only the family of sources, so
that the notion can be used on a big site as well as on a small one. In the Zariski case a
member is required to identify with a basic open of the target *together with* its immersion
map, which is what makes a standard Zariski covering a covering in the sense above.

## References

* [Stacks Project, Tag 03X8](https://stacks.math.columbia.edu/tag/03X8)
* [Stacks Project, Tag 03X9](https://stacks.math.columbia.edu/tag/03X9)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- The five topologies admitting standard affine coverings. -/
public inductive CoveringTopology where
  | fppf | syntomic | smooth | etale | zariski
  deriving DecidableEq

/-- The property required of morphisms in a covering family for the selected topology. -/
@[stacks 03X8 "morphism property for each topology"]
public abbrev coveringMorphismProperty (τ : CoveringTopology) :
    MorphismProperty Scheme.{u} :=
  match τ with
  | .fppf => @Flat ⊓ @LocallyOfFinitePresentation
  | .syntomic => @Syntomic
  | .smooth => @Smooth
  | .etale => @Etale
  | .zariski => @IsOpenImmersion

add_to_stacks 03X8 "precoverage of jointly surjective families"
  AlgebraicGeometry.Scheme.precoverage
add_to_sga "4 IV 8.5.5" "more general" AlgebraicGeometry.Scheme.precoverage
add_to_stacks 03X8 "joint surjectivity and componentwise property"
  AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff
add_to_sga "3 IV 6.1" "more general" AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff
add_to_sga "4 VII 1.2" "more general" AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff

/-- A finite family of affine schemes covering an affine target, with morphisms of the standard
form appropriate to the chosen topology. -/
@[stacks 03X9]
public structure IsStandardCovering (τ : CoveringTopology) {T : Scheme.{u}} [IsAffine T]
    {I : Type v} (U : I → Scheme.{u}) (f : ∀ i, U i ⟶ T) : Prop where
  /-- The family has finitely many members. -/
  finite_index : Finite I
  /-- Every source is affine. -/
  affine_source : ∀ i, IsAffine (U i)
  /-- The images of the members cover the target. -/
  jointly_surjective : (⋃ i, Set.range (f i)) = Set.univ
  /-- Every member has the standard affine form attached to the topology. -/
  standard : ∀ i,
    match τ with
    | .fppf => Flat (f i) ∧ FinitePresentation (f i)
    | .syntomic => @IsStandardSyntomic (U i) T (affine_source i) inferInstance (f i)
    | .smooth => @IsStandardSmooth (U i) T (affine_source i) inferInstance (f i)
    | .etale => Etale (f i)
    | .zariski => ∃ a : Γ(T, ⊤), ∃ e : U i ≅ (T.basicOpen a).toScheme,
        f i = e.hom ≫ (T.basicOpen a).ι

end AlgebraicGeometry
