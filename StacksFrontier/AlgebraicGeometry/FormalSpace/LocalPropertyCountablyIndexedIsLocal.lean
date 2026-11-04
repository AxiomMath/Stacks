module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.IsomorphismInvariantSourceTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyCountablyIndexed

/-!
# Stacks 0ANG for a local property in the sense of Situation 0CBA

Situation 0CBA opens with "let `P` be a property of morphisms of `WAdm^count`, invariant under
isomorphism of source and target in this category", and then asks for the three axioms 0AND,
0ANE and 0ANF. Both clauses together are `TopologicalRing.PropertyIsLocal'` at the class
`TopologicalRing.IsCountablyWeaklyAdmissible`: its field `isomorphismInvariant` is the opening
clause and its other three fields are the axioms.

This file states **Stacks 0ANG** for such a `P`. The invariance under isomorphism of sources and
of targets used by `AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_isLocallyCountablyIndexed`
is derived from the opening clause by
`AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderSourceIso_of_isomorphismInvariant` and
`AlgebraicGeometry.FormalSpace.propertyIsInvariantUnderTargetIsoOn_of_isomorphismInvariant`, so
that nothing beyond the source's notion of a local property is assumed.

## Main results

* `AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_isLocallyCountablyIndexed_of_isLocal`:
  **Stacks 0ANG**.

## References

* [Stacks Project, Tag 0CBA](https://stacks.math.columbia.edu/tag/0CBA)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-- **Stacks 0ANG.** Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of locally
countably indexed formal algebraic spaces over `S`. Let `P` be a local property of morphisms of
`WAdm^count` in the sense of Situation 0CBA: invariant under isomorphism of source and target in
`WAdm^count`, and satisfying the axioms 0AND, 0ANE and 0ANF; this is
`TopologicalRing.PropertyIsLocal' P TopologicalRing.IsCountablyWeaklyAdmissible`. The following
are equivalent:

1. for every commutative diagram with `U` and `V` affine formal algebraic spaces and `U ⟶ X`,
   `V ⟶ Y` representable by algebraic spaces and étale, the morphism `U ⟶ V` corresponds to a
   morphism of `WAdm^count` with property `P`;
2. there is a covering `{Vⱼ ⟶ Y}` as in Definition 0AIM and for each `j` a covering
   `{Uᵢ ⟶ Vⱼ ×_Y X}` as in Definition 0AIM such that each `Uᵢ ⟶ Vⱼ` corresponds to a morphism of
   `WAdm^count` with property `P`;
3. there are a covering `{Uᵢ ⟶ X}` as in Definition 0AIM and for each `i` a factorization
   `Uᵢ ⟶ Vᵢ ⟶ Y` where `Vᵢ` is an affine formal algebraic space, `Vᵢ ⟶ Y` is representable by
   algebraic spaces and étale, and `Uᵢ ⟶ Vᵢ` corresponds to a morphism of `WAdm^count` with
   property `P`.

This is `AlgebraicGeometry.FormalSpace.hasProperty_tfae_of_isLocallyCountablyIndexed`, whose
invariance under isomorphism of sources and of targets is derived from the invariance clause of
Situation 0CBA. -/
@[stacks 0ANG "the equivalence of conditions (1), (2) and (3) for a morphism of locally \
countably indexed formal algebraic spaces and a local property of WAdm^count in the sense of \
Situation 0CBA (invariance under isomorphism of source and target, and the axioms 0AND, 0ANE, \
0ANF)"]
theorem hasProperty_tfae_of_isLocallyCountablyIndexed_of_isLocal
    (hP : TopologicalRing.PropertyIsLocal' P TopologicalRing.IsCountablyWeaklyAdmissible)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y) :
    List.TFAE
      [ HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible P f,
        HasPropertyAfterTargetCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f,
        HasPropertyAfterSourceCover B S hS TopologicalRing.IsCountablyWeaklyAdmissible P f ] :=
  hasProperty_tfae_of_isLocallyCountablyIndexed B S hS P hP.toPropertyIsLocal
    (propertyIsInvariantUnderSourceIso_of_isomorphismInvariant hP.isomorphismInvariant)
    (propertyIsInvariantUnderTargetIsoOn_of_isomorphismInvariant hP.isomorphismInvariant) f hX hY

end AlgebraicGeometry.FormalSpace

end
