module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Transporting epimorphy of sheaves of modules across the pullback–pushforward adjunction

A morphism out of a pullback `f^* M` of sheaves of modules is hard to handle directly: the
pullback is a sheafification of a tensor product and has no usable description of its sections.
Its adjoint transpose `M ⟶ f_* N` is concrete. This file shows that for a morphism `f` of
schemes whose underlying map of spaces is a topological embedding — in particular for a closed
immersion — epimorphy transfers from the transpose to the morphism itself.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistEpi.faithful_pushforward`: `f_*` is faithful as soon as
  every open of the source is an inverse image.
* `Stacks.AlgebraicGeometry.ProjTwistEpi.exists_preimage_opens_of_isInducing`: inducedness of
  `f` on spaces supplies that hypothesis.
* `Stacks.AlgebraicGeometry.ProjTwistEpi.epi_homEquiv_symm_of_epi`: for an adjunction with
  faithful right adjoint, the inverse transpose of an epimorphism is an epimorphism.

## References

* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Stacks.AlgebraicGeometry.ProjTwistEpi

universe u

/-- Every open of the source of a morphism of schemes whose base map is inducing is the inverse
image of an open of the target. -/
public theorem exists_preimage_opens_of_isInducing {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : Topology.IsInducing f.base) (V : X.Opens) : ∃ W : Y.Opens, f ⁻¹ᵁ W = V := by
  obtain ⟨t, ht, hts⟩ := hf.isOpen_iff.1 V.2
  exact ⟨⟨t, ht⟩, TopologicalSpace.Opens.ext hts⟩

/-- **The pushforward of sheaves of modules along an embedding is faithful.** The pushforward
along a morphism of schemes `f` is faithful when every open of the source is the inverse image
under `f` of an open of the target. -/
public theorem faithful_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : ∀ V : X.Opens, ∃ W : Y.Opens, f ⁻¹ᵁ W = V) :
    (Scheme.Modules.pushforward f).Faithful := by
  constructor
  intro M N φ φ' h
  refine Scheme.Modules.hom_ext φ φ' fun V => ?_
  obtain ⟨W, hW⟩ := hf V
  subst hW
  exact congrArg (fun ψ => Scheme.Modules.Hom.app ψ W) h

/-- **Epimorphy transfers from the transpose.** For an adjunction `L ⊣ R` with faithful right
adjoint, if the transpose `g : X ⟶ R Y` of a morphism `L X ⟶ Y` is an epimorphism then so is the
morphism itself. -/
public theorem epi_homEquiv_symm_of_epi {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [R.Faithful] {X : C} {Y : D} (g : X ⟶ R.obj Y)
    (hg : Epi g) : Epi ((adj.homEquiv X Y).symm g) := by
  have h0 : adj.homEquiv X Y ((adj.homEquiv X Y).symm g) = g :=
    (adj.homEquiv X Y).apply_symm_apply g
  rw [Adjunction.homEquiv_unit] at h0
  have h1 : Epi (adj.unit.app X ≫ R.map ((adj.homEquiv X Y).symm g)) := by
    rwa [h0]
  exact R.epi_of_epi_map (epi_of_epi (adj.unit.app X) _)

end Stacks.AlgebraicGeometry.ProjTwistEpi

end
