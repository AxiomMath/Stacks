module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ConnectedComponentSection.FibreComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic

/-!
# Geometric irreducibility across a universal homeomorphism

A universal homeomorphism is universally open and geometrically irreducible, and precomposition
with a universal homeomorphism `u : A ⟶ B` does not change geometric irreducibility of a morphism
`q : B ⟶ S`, nor of its fibres.

## Main results

* `AlgebraicGeometry.universallyOpen_of_universalHomeomorphism`: a universal homeomorphism is
  universally open.
* `AlgebraicGeometry.geometricallyIrreducible_of_universalHomeomorphism`: a universal
  homeomorphism is geometrically irreducible.
* `AlgebraicGeometry.geometricallyIrreducible_comp_iff_of_universalHomeomorphism`: `u ≫ q` is
  geometrically irreducible if and only if `q` is.
* `AlgebraicGeometry.universalHomeomorphism_fiberMapOfSourceHom`: the comparison morphism from the
  fibre of `u ≫ q` to the fibre of `q` is a universal homeomorphism.
* `AlgebraicGeometry.geometricallyIrreducible_fiber_comp_iff_of_universalHomeomorphism`: the fibre
  of `u ≫ q` at `s` is geometrically irreducible if and only if that of `q` is.

## References

* [Stacks Project, Tag 04DD](https://stacks.math.columbia.edu/tag/04DD)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {A B S : Scheme.{u}}

/-- A universal homeomorphism is universally open. -/
theorem universallyOpen_of_universalHomeomorphism (u : A ⟶ B) [UniversalHomeomorphism u] :
    UniversallyOpen u :=
  ⟨fun _ _ i₁ i₂ f' h ↦
    (UniversalHomeomorphism.universally_isHomeomorph (f := u) i₁ i₂ f' h).isOpenMap⟩

/-- The base change of a universal homeomorphism is a homeomorphism. -/
private theorem isHomeomorph_pullback_snd (u : A ⟶ B) [UniversalHomeomorphism u] {Z : Scheme.{u}}
    (g : Z ⟶ B) : IsHomeomorph (pullback.snd u g) :=
  UniversalHomeomorphism.universally_isHomeomorph (f := u) _ _ _
    (IsPullback.of_hasPullback u g).flip

/-- A universal homeomorphism is geometrically irreducible. -/
theorem geometricallyIrreducible_of_universalHomeomorphism (u : A ⟶ B)
    [UniversalHomeomorphism u] : GeometricallyIrreducible u := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y ↦ ?_⟩
  exact (IsHomeomorph.homeomorph _ (isHomeomorph_pullback_snd u y)).irreducibleSpace_iff.mpr
    inferInstance

/-- The base change of `u ≫ q` to the spectrum of a field is homeomorphic to the base change of
`q`, when `u` is a universal homeomorphism. -/
private theorem irreducibleSpace_pullback_comp_iff (u : A ⟶ B) (q : B ⟶ S)
    [UniversalHomeomorphism u] {K : Type u} [Field K] (y : Spec (.of K) ⟶ S) :
    IrreducibleSpace ↥(pullback (u ≫ q) y) ↔ IrreducibleSpace ↥(pullback q y) := by
  exact ((pullbackRightPullbackFstIso q y u).hom.homeomorph.irreducibleSpace_iff).symm.trans
    (IsHomeomorph.homeomorph _ (isHomeomorph_pullback_snd u _)).irreducibleSpace_iff

/-- Precomposition with a universal homeomorphism does not change geometric irreducibility. -/
theorem geometricallyIrreducible_comp_iff_of_universalHomeomorphism (u : A ⟶ B) (q : B ⟶ S)
    [UniversalHomeomorphism u] :
    GeometricallyIrreducible (u ≫ q) ↔ GeometricallyIrreducible q := by
  rw [GeometricallyIrreducible.eq_geometrically,
    geometrically_iff_of_isClosedUnderIsomorphisms (f := u ≫ q),
    geometrically_iff_of_isClosedUnderIsomorphisms (f := q)]
  exact ⟨fun h K _ y ↦ (irreducibleSpace_pullback_comp_iff u q y).mp (h K y),
    fun h K _ y ↦ (irreducibleSpace_pullback_comp_iff u q y).mpr (h K y)⟩

/-- The comparison morphism from the fibre of `u ≫ q` to the fibre of `q` is a universal
homeomorphism as soon as `u` is. -/
theorem universalHomeomorphism_fiberMapOfSourceHom (u : A ⟶ B) (q : B ⟶ S)
    [UniversalHomeomorphism u] (s : S) :
    UniversalHomeomorphism (fiberMapOfSourceHom u q s) :=
  ⟨(MorphismProperty.universally_isStableUnderBaseChange
      (topologically @IsHomeomorph)).of_isPullback
      (fiberMapOfSourceHom_isPullback u q s).flip
      (UniversalHomeomorphism.universally_isHomeomorph (f := u))⟩

/-- Precomposition with a universal homeomorphism does not change geometric irreducibility of
the fibres. -/
theorem geometricallyIrreducible_fiber_comp_iff_of_universalHomeomorphism (u : A ⟶ B) (q : B ⟶ S)
    [UniversalHomeomorphism u] (s : S) :
    GeometricallyIrreducible ((u ≫ q).fiberToSpecResidueField s) ↔
      GeometricallyIrreducible (q.fiberToSpecResidueField s) := by
  have := universalHomeomorphism_fiberMapOfSourceHom u q s
  rw [← fiberMapOfSourceHom_fiberToSpecResidueField u q s]
  exact geometricallyIrreducible_comp_iff_of_universalHomeomorphism _ _

end AlgebraicGeometry

end
