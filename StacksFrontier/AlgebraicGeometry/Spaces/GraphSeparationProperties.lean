module

public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# Properties of the graph of a morphism of algebraic spaces

Let `S` be a scheme, let `Z` be an algebraic space over `S`, and let `f : X ⟶ Y` be a
morphism of algebraic spaces over `Z`.  The graph of `f` is the morphism
`X ⟶ X ×[Z] Y` with components the identity of `X` and `f`; it is
`AlgebraicGeometry.Space.graph`.  This file states the four parts of Stacks 03KO as a single
result about that morphism: it is always representable, locally of finite type, locally
quasi-finite, separated and a monomorphism, and it is an immersion, a closed immersion or
quasi-compact as soon as `Y ⟶ Z` is locally separated, separated or quasi-separated.

Parts (2), (3) and (4) are conditions on `Y ⟶ Z`, so inside the single statement they appear
as implications with those separation properties as their antecedents, which is the form the
source gives them in.

## Main results

* `AlgebraicGeometry.Space.separationProperties_graph`: the whole of Stacks 03KO, all four
  parts, for the graph of a morphism of algebraic spaces over an algebraic space.

## References

* [Stacks Project, Tag 03KO](https://stacks.math.columbia.edu/tag/03KO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03KO.** Let `Z` be an algebraic space over the scheme `S` and let `f : X ⟶ Y` be
a morphism of algebraic spaces over `Z`.  For the graph `i : X ⟶ X ×[Z] Y` of `f`:

1. `i` is representable, locally of finite type, locally quasi-finite, separated and a
   monomorphism;
2. if `Y ⟶ Z` is locally separated then `i` is an immersion;
3. if `Y ⟶ Z` is separated then `i` is a closed immersion; and
4. if `Y ⟶ Z` is quasi-separated then `i` is quasi-compact.

The graph is a section of the first projection of `X ×[Z] Y`, and all four parts are the
corresponding parts of Stacks 03KP for that section; parts (2), (3) and (4) use in addition
that the first projection inherits the relevant separation property from `Y ⟶ Z` as a base
change of it. -/
@[stacks 03KO]
theorem separationProperties_graph {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) :
    (yoneda.relativelyRepresentable (graph B S hS f g) ∧
        IsLocallyOfFiniteType B S hS (graph B S hS f g) ∧
        IsLocallyQuasiFinite B S hS (graph B S hS f g) ∧
        IsSeparated B S hS (graph B S hS f g) ∧
        Mono (graph B S hS f g)) ∧
      (IsLocallySeparated B S hS g → IsImmersion B S hS (graph B S hS f g)) ∧
      (IsSeparated B S hS g → IsClosedImmersion B S hS (graph B S hS f g)) ∧
      (IsQuasiSeparated B S hS g → IsQuasiCompact B S hS (graph B S hS f g)) :=
  ⟨⟨relativelyRepresentable_graph B S hS f g hX hY hZ,
      isLocallyOfFiniteType_graph B S hS f g hX hY hZ,
      isLocallyQuasiFinite_graph B S hS f g hX hY hZ,
      isSeparated_graph B S hS f g, mono_graph B S hS f g⟩,
    isImmersion_graph_of_isLocallySeparated B S hS f g,
    isClosedImmersion_graph_of_isSeparated B S hS f g,
    isQuasiCompact_graph_of_isQuasiSeparated B S hS f g⟩

end AlgebraicGeometry.Space

end
