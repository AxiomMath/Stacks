module

public import Mathlib.GroupTheory.Finiteness
public import StacksFrontier.Deformation.Cofibered.Over
public import StacksFrontier.Deformation.Examples.Linear.RepresentationsCofibered
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.Terminal

/-!
# The functor of isomorphism classes of deformations of a representation

Fix a complete Noetherian local coefficient ring `Λ` with residue field `k`, a finitely
generated group `Γ` and a finite-dimensional representation `ρ₀` of `Γ` on a `k`-vector space
`V`. The deformation category of `ρ₀` — finite projective representations of `Γ` over an object
of `𝒞_Λ` equipped with an identification of the special fibre with `(V, ρ₀)` — is cofibered in
groupoids over `𝒞_Λ`, so it has an associated covariant functor on `𝒞_Λ` whose value at `A` is
the set of isomorphism classes of deformations of `ρ₀` over `A`. That functor is the object whose
prorepresentability and hull are the content of Stacks Project, Tag 0ET1.

## Main definitions

* `Deformation.Examples.RepresentationDeformationSituation`: the standing data of the problem —
  a finitely generated group, a finite-dimensional representation of it over `k`, and the
  hypothesis that `𝒞_Λ` is in the classical case.
* `Deformation.Examples.RepresentationDeformationSituation.deformationProjection`: the structure
  functor of the deformation category of `ρ₀` over `𝒞_Λ`.
* `Deformation.Examples.RepresentationDeformationSituation.isomorphismClassFunctor`: the
  associated functor of fibrewise isomorphism classes of deformations of `ρ₀`.

## Main results

* `Deformation.Examples.RepresentationDeformationSituation`'s
  `deformationProjection_isCofiberedInGroupoids`: the deformation category of `ρ₀` is cofibered
  in groupoids over `𝒞_Λ`, which is what the isomorphism-class functor is formed from.

## Implementation notes

The deformation category is the slice category of the category of all finite projective
representations of `Γ` at the object `(k, V, ρ₀)`, and its structure functor is the slice
projection composed with the functor forgetting the module and the action. Its cofibered
structure is therefore a special case of `Deformation.isCofiberedInGroupoids_overForget`: the
base of `(k, V, ρ₀)` is the residue field `k` itself, which is a terminal object of `𝒞_Λ`, so no
hypothesis beyond the cofibered structure of the ambient representation category is needed.

Finite-dimensionality of `V` is a field of the standing data rather than an ambient instance,
because the special-fibre object cannot be formed without it; it is therefore introduced as a
local instance both in the type and in the body of the structure functor.

## References

* [Stacks Project, Tag 0D3J](https://stacks.math.columbia.edu/tag/0D3J)
* [Stacks Project, Tag 0ET1](https://stacks.math.columbia.edu/tag/0ET1)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.Examples

universe u w g m

/-- The standing data for the deformation theory of a representation: a finitely generated
group `Γ`, a finite-dimensional representation of `Γ` on the `k`-vector space `V`, and the
hypothesis that the base category `𝒞_Λ` is in the classical case, i.e. that `Λ` is a complete
Noetherian local ring with residue field `k`. -/
public structure RepresentationDeformationSituation
    (Λ : Type u) (k : Type w) (Γ : Type g) (V : Type (max w m))
    [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ]
    [AddCommGroup V] [Module k V] where
  /-- The group is finitely generated. -/
  finiteGeneration : Group.FG Γ
  /-- The representation space is finite-dimensional over `k`. -/
  finiteDimensional : Module.Finite k V
  /-- The base category `𝒞_Λ` is in the classical case. -/
  classical : IsClassical Λ k
  /-- The representation being deformed. -/
  representation : Representation k Γ V

namespace RepresentationDeformationSituation

variable {Λ : Type u} {k : Type w} {Γ : Type g} {V : Type (max w m)}
  [CommRing Λ] [Field k] [Algebra Λ k] [Group Γ] [AddCommGroup V] [Module k V]

/-- The structure functor of the deformation category of the given representation: it sends a
deformation to its coefficient algebra, and is the slice projection of the category of finite
projective representations of `Γ` at the special-fibre object `(k, V, ρ₀)`. -/
public noncomputable def deformationProjection
    (S : RepresentationDeformationSituation Λ k Γ V) :
    letI : Module.Finite k V := S.finiteDimensional
    FiniteProjectiveRepresentation.deformationCategory (Λ := Λ) V S.representation ⥤
      ArtinianLocalAlgCat.{u, w, w} Λ k :=
  letI : Module.Finite k V := S.finiteDimensional
  objectsOverFunctor FiniteProjectiveRepresentation.projection
    (FiniteProjectiveRepresentation.specialFiber (Λ := Λ) V S.representation)

/-- The deformation category of a finite-dimensional representation is cofibered in groupoids
over `𝒞_Λ`. The coefficient algebra of the special-fibre object is the residue field `k`, which
is a terminal object of `𝒞_Λ`, so this is the terminal-base case of slicing a category cofibered
in groupoids at an object. -/
public theorem deformationProjection_isCofiberedInGroupoids
    (S : RepresentationDeformationSituation Λ k Γ V) :
    IsCofiberedInGroupoids S.deformationProjection := by
  let : Module.Finite k V := S.finiteDimensional
  exact isCofiberedInGroupoids_overForget
    FiniteProjectiveRepresentation.projection_isCofiberedInGroupoids
    (FiniteProjectiveRepresentation.specialFiber (Λ := Λ) V S.representation)
    (ArtinianLocalAlgCat.isTerminal_of_algEquiv _ AlgEquiv.refl)

/-- The functor on `𝒞_Λ` whose value at a coefficient algebra `A` is the set of isomorphism
classes of deformations of the given representation over `A`, with the pushforward maps induced
by extension of scalars. -/
public noncomputable def isomorphismClassFunctor
    (S : RepresentationDeformationSituation Λ k Γ V) :
    ArtinianLocalAlgCat.{u, w, w} Λ k ⥤ Type (max (max (max g (m + 1)) u) (w + 1)) :=
  isomorphismClasses (BasedCategory.ofFunctor S.deformationProjection)
    S.deformationProjection_isCofiberedInGroupoids

end RepresentationDeformationSituation

end Deformation.Examples

end
