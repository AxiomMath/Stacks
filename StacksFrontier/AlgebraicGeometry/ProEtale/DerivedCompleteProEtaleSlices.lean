module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SmallSiteSituation

/-!
# The sliced situation of testing objects on the small pro-étale site

`AlgebraicGeometry.Scheme.ProEt.weaklyContractibleObjectsSituation` fixes the affine weakly
contractible objects of the small pro-étale site `X_proétale` and records that a locally
surjective morphism of sheaves of sets in `Type (u + 1)` is surjective on sections over each of
them. The derived-completeness results need the same statement on every slice site
`X_proétale/W`, since derived completeness of a complex of sheaves of modules is a condition on
its restriction to the slices. This file proves it and assembles
`Stacks.WeaklyContractible.SlicedObjectsSituation` for this site.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.surjective_sections_over_of_isWContractible`: an object of a
  slice of the small pro-étale site whose source is affine with w-contractible ring of global
  sections tests surjectivity of morphisms of sheaves of sets on that slice, in any universe of
  values.
* `AlgebraicGeometry.Scheme.ProEt.slicedObjectsSituation`: the sliced bundle for the small
  pro-étale site, with the affine weakly contractible objects as its collection.

## References

* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 0990](https://stacks.math.columbia.edu/tag/0990)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe t w u

namespace AlgebraicGeometry.Scheme.ProEt

variable {X : Scheme.{u}}

/-- **An object of a slice of the small pro-étale site with affine, w-contractible source tests
surjectivity of morphisms of sheaves of sets**, in any universe of values: for `W : X.ProEt` and
`Z : Over W` whose underlying scheme `Z.left.left` is affine with w-contractible ring of global
sections, a locally surjective morphism of sheaves of sets on `(ProEt.topology X).over W` is
surjective on sections over `Z`. -/
theorem surjective_sections_over_of_isWContractible (W : X.ProEt) (Z : Over W)
    [IsAffine Z.left.left] (hZ : IsWContractible.{u, u} Γ(Z.left.left, ⊤))
    (F G : Sheaf ((ProEt.topology X).over W) (Type t)) (φ : F ⟶ G)
    (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op Z)) := by
  classical
  refine GrothendieckTopology.surjective_sections_of_clopenRefinements
    ((ProEt.topology X).over W)
    (Over.forget W ⋙ ProEtale.proetaleToScheme X) Z (fun Y hY ↦ ?_) (fun f hf ↦ ?_) ?_ F G φ hφ
  · rw [GrothendieckTopology.mem_over_iff, map_bot]
    have _ : IsEmpty Y.left.left := hY
    exact ProEt.bot_mem_topology Y.left
  · exact (Over.forget W ⋙ ProEtale.proetaleToScheme X).mono_of_mono_map hf
  · intro S hS
    rw [GrothendieckTopology.mem_over_iff] at hS
    obtain ⟨n, V, g, hdec, hcov, hmem⟩ :=
      exists_clopenRefinement_of_isWContractible Z.left hZ (Sieve.overEquiv Z S) hS
    refine ⟨n, fun i ↦ Over.mk (g i ≫ Z.hom), fun i ↦ Over.homMk (g i), hdec, ?_, ?_⟩
    · rwa [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    · exact fun i ↦ (Sieve.overEquiv_iff S (g i)).mp (hmem i)

/-- **The affine weakly contractible objects of the small pro-étale site of `X`, together with a
sheaf of rings on that site, form a `Stacks.WeaklyContractible.SlicedObjectsSituation`**: they
cover the site, they test surjectivity of sheaves of sets in `Type (u + 1)` there, and the arrows
of the site with such a source test it on the slice sites. -/
def slicedObjectsSituation (X : Scheme.{u}) (O : Sheaf (ProEt.topology X) RingCat.{w}) :
    _root_.Stacks.WeaklyContractible.SlicedObjectsSituation.{w, u, u + 1, u + 1}
      X.ProEt (ProEt.topology X) where
  toWeaklyContractibleObjectsSituation := weaklyContractibleObjectsSituation X O
  isWeaklyContractibleOver W {Z} hZ F G φ hφ :=
    have _ : IsAffine Z.left.left := hZ.1
    surjective_sections_over_of_isWContractible W Z
      (isWContractible_globalSections_of_isWeaklyContractible Z.left hZ.2) F G φ hφ

end AlgebraicGeometry.Scheme.ProEt

end
