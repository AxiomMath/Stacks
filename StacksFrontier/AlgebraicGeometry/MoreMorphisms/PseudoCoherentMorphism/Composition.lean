module

public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composition and cancellation for pseudo-coherent morphisms

Pseudo-coherence of morphisms of schemes is stable under composition, and it descends from a
common base: a morphism between two schemes that are both pseudo-coherent over a base scheme is
itself pseudo-coherent.

## Main results

* `AlgebraicGeometry.pseudoCoherent_comp`: **Stacks 0681**, a composition of pseudo-coherent
  morphisms of schemes is pseudo-coherent.
* `AlgebraicGeometry.pseudoCoherent_of_comp`: **Stacks 0683**, a morphism `f : X ⟶ Y` between two
  schemes pseudo-coherent over a base `S` is pseudo-coherent.

## Implementation notes

Both statements reduce to their algebra counterparts, which are `Algebra.PseudoCoherent.trans`
and `Algebra.PseudoCoherent.of_restrictScalars`, through
`AlgebraicGeometry.hasRingHomProperty_pseudoCoherent`.

For Stacks 0681 the reduction is `AlgebraicGeometry.HasRingHomProperty.stableUnderComposition`
applied to `RingHom.pseudoCoherent_stableUnderComposition`; this is the same shape as
`AlgebraicGeometry.LocallyOfFiniteType`, and the `MorphismProperty.IsStableUnderComposition`
instance is recorded alongside the `PseudoCoherent (f ≫ g)` instance that typeclass inference
uses.

For Stacks 0683 the general `AlgebraicGeometry.HasRingHomProperty.of_comp` does not apply: its
hypothesis asks that pseudo-coherence of a composite of ring maps imply pseudo-coherence of the
second factor unconditionally, which is false, whereas the source's statement also assumes that
`Y` is pseudo-coherent over `S`. Instead pseudo-coherence of `f` is checked around each point of
`X` with `AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE`: given `x`, choose an affine open
`W ⊆ S` around its image, then an affine open `V ⊆ g ⁻¹ᵁ W` around the image of `x` in `Y`, then an
affine open `U ⊆ f ⁻¹ᵁ V` around `x`. The hypotheses give pseudo-coherence of `Γ(S, W) ⟶ Γ(Y, V)`
and of `Γ(S, W) ⟶ Γ(X, U)`, whose composite the second is by `Scheme.Hom.appLE_comp_appLE`, and
the algebra cancellation lemma concludes for `Γ(Y, V) ⟶ Γ(X, U)`.

## References

* [The Stacks Project, Lemma 37.60.4 (0681)](https://stacks.math.columbia.edu/tag/0681)
* [The Stacks Project, Lemma 37.60.7 (0683)](https://stacks.math.columbia.edu/tag/0683)
* [The Stacks Project, Lemma 15.83.11 (067D)](https://stacks.math.columbia.edu/tag/067D)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace RingHom

/-- **The algebra content of Stacks 0683**, stated for `RingHom.PseudoCoherent`. If `f : R →+* A`
and `g.comp f : R →+* B` are pseudo-coherent, then so is `g : A →+* B`.

This is `Algebra.PseudoCoherent.of_restrictScalars` transported along `RingHom.toAlgebra`. -/
theorem PseudoCoherent.of_comp {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (g : A →+* B) (hf : PseudoCoherent f) (hfg : PseudoCoherent (g.comp f)) :
    PseudoCoherent g := by
  algebraize_only [f, g, g.comp f]
  exact hf.of_restrictScalars hfg

end RingHom

namespace AlgebraicGeometry

/-- Pseudo-coherence of morphisms of schemes is stable under composition, because pseudo-coherence
of ring maps is; this is `AlgebraicGeometry.pseudoCoherent_comp`, Stacks 0681, in the form of a
`MorphismProperty` statement. -/
@[sga "6 III 1.14" "special case"]
instance pseudoCoherent_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @PseudoCoherent :=
  HasRingHomProperty.stableUnderComposition RingHom.pseudoCoherent_stableUnderComposition

/-- **Stacks 0681.** A composition of pseudo-coherent morphisms of schemes is pseudo-coherent. -/
@[stacks 0681]
instance pseudoCoherent_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : PseudoCoherent f] [hg : PseudoCoherent g] : PseudoCoherent (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

/-- **Stacks 0683.** If `X` and `Y` are pseudo-coherent over a base scheme `S`, then any morphism
`f : X ⟶ Y` over `S` is pseudo-coherent.

Pseudo-coherence of `f` is checked around a point `x` of `X` on an affine open `U ∋ x` of `X`
contained in the preimage of an affine open `V` of `Y`, itself contained in the preimage of an
affine open `W` of `S`. The map `Γ(S, W) ⟶ Γ(X, U)` is the composite of `Γ(S, W) ⟶ Γ(Y, V)` with
`Γ(Y, V) ⟶ Γ(X, U)`, and the outer two are pseudo-coherent by hypothesis, so the algebra
cancellation lemma applies. -/
@[stacks 0683, sga "6 III 1.14" "special case"]
theorem pseudoCoherent_of_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [PseudoCoherent (f ≫ g)] [PseudoCoherent g] : PseudoCoherent f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @PseudoCoherent)
    RingHom.pseudoCoherent_stableUnderCompositionWithLocalizationAway.left]
  intro x
  have hmem : g.base (f.base x) ∈ (⨆ W : S.affineOpens, (W : S.Opens)) := by
    rw [iSup_affineOpens_eq_top]; trivial
  obtain ⟨W, hxW⟩ := Opens.mem_iSup.mp hmem
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show f.base x ∈ g ⁻¹ᵁ (W : S.Opens) from hxW) (g ⁻¹ᵁ (W : S.Opens)).2
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ V from hxV) (f ⁻¹ᵁ V).2
  refine ⟨⟨V, hV⟩, ⟨U, hU⟩, hxU, hUV, RingHom.PseudoCoherent.of_comp
    (g.appLE (W : S.Opens) V hVW).hom (f.appLE V U hUV).hom
    (HasRingHomProperty.appLE @PseudoCoherent g ‹_› W ⟨V, hV⟩ hVW) ?_⟩
  have h := HasRingHomProperty.appLE @PseudoCoherent (f ≫ g) ‹_› W ⟨U, hU⟩
    (hUV.trans ((Opens.map f.base).map (homOfLE hVW)).le)
  rwa [← Scheme.Hom.appLE_comp_appLE f g (W : S.Opens) V U hVW hUV, CommRingCat.hom_comp] at h

end AlgebraicGeometry

end
