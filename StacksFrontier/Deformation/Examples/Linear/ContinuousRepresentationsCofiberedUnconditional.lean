module

public import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsCofibered
public import StacksFrontier.Deformation.Representation.Cofibered

/-!
# Continuous representations are cofibered in groupoids, unconditionally (Stacks 0D3K)

`StacksFrontier/Deformation/Examples/Linear/ContinuousRepresentationsCofibered.lean` proves that
the category `ℱ` of continuous finite projective representations of a topological group `Γ` is
cofibered in groupoids over `𝒞_Λ` given that the ambient category of finite projective
representations is. This file removes that hypothesis.

## Main results

* `isCofiberedInGroupoids_continuousProjection`: the functor `p : ℱ → 𝒞_Λ` of Stacks 0D3K is
  cofibered in groupoids, for an arbitrary module universe and with no further hypothesis.

## Implementation notes

Cofiberedness of the ambient category is taken from the second presentation
`Deformation.RepresentationCategory` of Stacks 0D3J rather than from
`Deformation.Examples.FiniteProjectiveRepresentation.projection_isCofiberedInGroupoids`,
because the latter restricts the module universe to one of the form `max v m`: its scalar
extension lands in the universe of the coefficient algebras. The second presentation carries
the base change back into the module universe along `Deformation.ArtinianLocalAlgCat.small`
and so holds for an arbitrary module universe, which is the generality the objects and the
projection of `ℱ` are stated in. The two presentations have the same fields, so the
comparison between them is an isomorphism of categories over `𝒞_Λ` whose round trips are the
identity on the nose.

## References

* [Stacks Project, Tag 0D3K](https://stacks.math.columbia.edu/tag/0D3K)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples.FiniteProjectiveRepresentation

universe u v w m

variable {Λ : Type u} {k : Type w} {Γ : Type*}
  [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [TopologicalSpace Γ]

omit [TopologicalSpace Γ] in
/-- Comparison with the second presentation `Deformation.RepresentationCategory` of the
category of Stacks 0D3J: the two structures carry the same fields, so reassembling them is a
functor, strictly over `𝒞_Λ`. -/
private def toRepresentationCategory :
    FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ ⥤
      RepresentationCategory.{u, v, w, m} Λ k Γ where
  obj X := { base := X.base, carrier := X.carrier, action := X.action }
  map f := { base := f.base, map := f.map, map_smul := f.map_smul,
             equivariant := f.equivariant, isBaseChange := f.isBaseChange }
  map_id _ := rfl
  map_comp _ _ := rfl

omit [TopologicalSpace Γ] in
/-- The inverse of `toRepresentationCategory`. Both round trips are the identity on the
nose, so the two presentations are isomorphic as categories over `𝒞_Λ`. -/
private def ofRepresentationCategory :
    RepresentationCategory.{u, v, w, m} Λ k Γ ⥤
      FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ where
  obj X := { base := X.base, carrier := X.carrier, action := X.action }
  map f := { base := f.base, map := f.map, map_smul := f.map_smul,
             equivariant := f.equivariant, isBaseChange := f.isBaseChange }
  map_id _ := rfl
  map_comp _ _ := rfl

omit [TopologicalSpace Γ] in
/-- The projection of the category of finite projective representations is cofibered in
groupoids, with the module universe `m` unrestricted.

`Deformation.Examples.FiniteProjectiveRepresentation.projection_isCofiberedInGroupoids`
proves this only for a module universe of the form `max v m`, because the scalar extension
it builds lands in the universe of the coefficient algebras. The second presentation
`Deformation.RepresentationCategory` of the same category has no such restriction — it
transports the base change back into the module universe along
`Deformation.ArtinianLocalAlgCat.small` — and the two presentations are isomorphic over
`𝒞_Λ`, so the statement transports across. -/
private theorem projection_isCofiberedInGroupoids_general :
    IsCofiberedInGroupoids
      (projection (Λ := Λ) (k := k) (Γ := Γ) :
        FiniteProjectiveRepresentation.{u, v, w, m} Λ k Γ ⥤
          ArtinianLocalAlgCat.{u, v, w} Λ k) := by
  have hp : IsCofiberedInGroupoids
      (representationProjection (Λ := Λ) (k := k) (Γ := Γ) :
        RepresentationCategory.{u, v, w, m} Λ k Γ ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) :=
    RepresentationCategory.representationProjection_isCofiberedInGroupoids
  refine isCofiberedInGroupoids_of_lifts ?_ ?_
  · intro A B f a ha
    obtain ⟨b, φ, hφ⟩ := exists_pushforward hp f (toRepresentationCategory.obj a) ha
    refine ⟨ofRepresentationCategory.obj b, ofRepresentationCategory.map φ, ?_⟩
    refine IsHomLift.of_fac' _ f (ofRepresentationCategory.map φ)
      (IsHomLift.domain_eq representationProjection f φ)
      (IsHomLift.codomain_eq representationProjection f φ) ?_
    exact IsHomLift.fac' representationProjection f φ
  · intro a b c φ ψ f h
    obtain ⟨χ, hχ, huniq⟩ := exists_unique_cofibered_factor hp
      (toRepresentationCategory.map φ) (toRepresentationCategory.map ψ) f h
    exact ⟨ofRepresentationCategory.map χ,
      ⟨hχ.1, congrArg ofRepresentationCategory.map hχ.2⟩, fun χ' hχ' =>
      congrArg ofRepresentationCategory.map
        (huniq (toRepresentationCategory.map χ')
          ⟨hχ'.1, congrArg toRepresentationCategory.map hχ'.2⟩)⟩

/-- The functor `p : ℱ → 𝒞_Λ` sending a continuous finite projective representation `(A, M, ρ)`
of the topological group `Γ` to its coefficient algebra `A` is cofibered in groupoids, for an
arbitrary module universe and with no hypothesis on the ambient projection of finite projective
representations. -/
@[stacks 0D3K "continuous_representation_category: p is cofibred in groupoids"]
public theorem isCofiberedInGroupoids_continuousProjection :
    IsCofiberedInGroupoids (continuousProjection.{u, v, w, m} (Λ := Λ) (k := k) (Γ := Γ)) :=
  continuousProjection_isCofiberedInGroupoids projection_isCofiberedInGroupoids_general

end Deformation.Examples.FiniteProjectiveRepresentation
