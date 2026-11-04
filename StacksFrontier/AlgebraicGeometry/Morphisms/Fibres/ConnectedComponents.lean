module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.Connected.CardComponents
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.IrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparablyClosed
public import StacksCore.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Connected components of the fibres of a morphism of schemes

For a morphism of schemes `f : X ⟶ Y` we count the geometric connected components of the fibre
over each point of `Y`. The count is independent of the chosen separably closed extension of
the residue field, and both it and the locus of geometrically connected fibres are unchanged by
arbitrary base change.

## Main definitions

* `AlgebraicGeometry.numGeometricConnectedComponents` counts the connected components of a
  geometric fibre, with values in `ℕ∞`.

## Main results

* `AlgebraicGeometry.geometricallyConnected_fiber_locus_pullback` identifies the geometrically
  connected fibre locus of a base-changed morphism with the inverse image of the original locus.
* `AlgebraicGeometry.enatCard_connectedComponents_fiberBaseChange` identifies the count obtained
  from any separably closed extension with the canonical count.
* `AlgebraicGeometry.numGeometricConnectedComponents_eq_of_isPullback` says that this function
  is preserved by base change.

## Implementation notes

The geometric-fibre construction `AlgebraicGeometry.geometricFiber` is shared with the count of
irreducible components. The canonical count uses the absolute separable closure of the residue
field. A base change is represented either by the canonical pullback projection
`pullback.snd f g` or by an arbitrary pullback square, so the results also apply to any chosen
model of the fibre product.

## References

* [Stacks Project, Tag 055E](https://stacks.math.columbia.edu/tag/055E)
* [Stacks Project, Tag 055F](https://stacks.math.columbia.edu/tag/055F)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 055E.** Formation of the locus where the fibres of a scheme morphism
are geometrically connected commutes with arbitrary base change. -/
@[stacks 055E]
theorem geometricallyConnected_fiber_locus_pullback
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    {y' : Y' |
        GeometricallyConnected ((pullback.snd f g).fiberToSpecResidueField y')} =
      g ⁻¹' {y : Y | GeometricallyConnected (f.fiberToSpecResidueField y)} := by
  ext y'
  show GeometricallyConnected ((pullback.snd f g).fiberToSpecResidueField y') ↔
    GeometricallyConnected (f.fiberToSpecResidueField (g y'))
  have h := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g) y'
  have he : GeometricallyConnected ((pullback.snd f g).fiberToSpecResidueField y') ↔
      GeometricallyConnected (pullback.snd (f.fiberToSpecResidueField (g y'))
        (Spec.map (g.residueFieldMap y'))) := by
    have : MorphismProperty.RespectsIso (@GeometricallyConnected : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [← h.isoPullback_hom_snd]
    exact MorphismProperty.cancel_left_of_respectsIso
      (P := (@GeometricallyConnected : MorphismProperty Scheme.{u})) h.isoPullback.hom
      (pullback.snd (f.fiberToSpecResidueField (g y')) (Spec.map (g.residueFieldMap y')))
  let : Algebra (Y.residueField (g y')) (Y'.residueField y') := (g.residueFieldMap y').hom.toAlgebra
  exact he.trans (geometricallyConnected_iff_baseChange_fieldExtension (Y.residueField (g y'))
    (Y'.residueField y') (f.fiberToSpecResidueField (g y'))).symm

variable {X Y : Scheme.{u}}

add_to_stacks 055F "geometric fibre" geometricFiber

private lemma enatCard_connectedComponents_pullback
    {k L : Type u} [Field k] [IsSepClosed k] [Field L] [Algebra k L] {Z : Scheme.{u}}
    (q : Z ⟶ Spec (.of k)) :
    ENat.card (ConnectedComponents
      ((pullback q (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme))) =
      ENat.card (ConnectedComponents Z) :=
  ENat.card_congr (Equiv.ofBijective _ (baseChange_connectedComponents_bijective k L q))

/-- Isomorphic schemes have the same number of connected components. -/
lemma enatCard_connectedComponents_iso
    {A B : Scheme.{u}} (e : A ≅ B) :
    ENat.card (ConnectedComponents A) = ENat.card (ConnectedComponents B) := by
  let e' := e.hom.homeomorph
  exact ENat.card_congr (e'.isQuotientMap.isCoinducing.connectedComponentsHomeomorph
    (fun y => e'.isConnected_preimage.mpr isConnected_singleton)).toEquiv

private lemma enatCard_connectedComponents_pullback_assoc
    {k L M : Type u} [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra L M]
    [IsScalarTower k L M] {Z : Scheme.{u}}
    (q : Z ⟶ Spec (.of k)) :
    ENat.card (ConnectedComponents
      ((pullback (pullback.snd q (Spec.map (CommRingCat.ofHom (algebraMap k L))))
        (Spec.map (CommRingCat.ofHom (algebraMap L M))) : Scheme))) =
      ENat.card (ConnectedComponents
        ((pullback q (Spec.map (CommRingCat.ofHom (algebraMap k M))) : Scheme))) := by
  apply enatCard_connectedComponents_iso
  convert pullbackLeftPullbackSndIso q
    (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (Spec.map (CommRingCat.ofHom (algebraMap L M))) using 1
  congr 2
  rw [← Spec.map_comp]
  congr 2
  show algebraMap k M = (algebraMap L M).comp (algebraMap k L)
  exact IsScalarTower.algebraMap_eq k L M

private lemma enatCard_connectedComponents_fiber_isPullback
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (i : X' ⟶ X) (g : Y' ⟶ Y) (h : IsPullback i f' f g) (y' : Y')
    (K : Type u) [Field K] [Algebra (Y'.residueField y') K]
    [Algebra (Y.residueField (g y')) K]
    (hK : algebraMap (Y.residueField (g y')) K =
      (algebraMap (Y'.residueField y') K).comp
        (g.residueFieldMap y').hom) :
    ENat.card (ConnectedComponents (geometricFiber f' y' K)) =
      ENat.card (ConnectedComponents (geometricFiber f (g y') K)) := by
  let : Algebra (Y.residueField (g y')) (Y'.residueField y') :=
    RingHom.toAlgebra (g.residueFieldMap y').hom
  have hf := isPullback_fiberToSpecResidueField_of_isPullback h y'
  let e := hf.isoPullback
  let i₁ := e.hom
  let E : geometricFiber f' y' K ⟶
      (pullback (pullback.snd (f.fiberToSpecResidueField (g y'))
        (Spec.map (g.residueFieldMap y')))
        (Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y') K))) : Scheme) :=
    pullback.map
    (f'.fiberToSpecResidueField y')
    (Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y') K)))
    (pullback.snd (f.fiberToSpecResidueField (g y'))
      (Spec.map (g.residueFieldMap y')))
    (Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y') K)))
    i₁ (𝟙 _) (𝟙 _) hf.isoPullback_hom_snd.symm (by simp)
  have : IsIso E := by
    dsimp only [E]
    have hi : IsIso i₁ := e.isIso_hom
    exact @CategoryTheory.Limits.pullback.map_isIso _ _ _ _ _ _ _ _
      (f'.fiberToSpecResidueField y')
      (Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y') K)))
      (inferInstance)
      (pullback.snd (f.fiberToSpecResidueField (g y'))
        (Spec.map (g.residueFieldMap y')))
      (Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y') K)))
      (inferInstance) i₁ (𝟙 _) (𝟙 _) _ _ hi (inferInstance) (inferInstance)
  have : IsScalarTower (Y.residueField (g y')) (Y'.residueField y') K :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ DFunLike.congr_fun hK x)
  exact (enatCard_connectedComponents_iso (asIso E)).trans
    (enatCard_connectedComponents_pullback_assoc
      (k := Y.residueField (g y')) (L := Y'.residueField y') (M := K)
      (f.fiberToSpecResidueField (g y')))

/-- The number of geometric connected components of each fibre of a morphism of schemes. -/
@[stacks 055F "the function",
  ega "III 4.3.4" "geom. # of components",
  ega "IV 15.5.3",
  ega "IV 4.5.2" "more general"]
def numGeometricConnectedComponents (f : X ⟶ Y) : Y → ℕ∞ := fun y ↦
  ENat.card (ConnectedComponents
    (geometricFiber f y (SeparableClosure (Y.residueField y))))

/-- Computing the number of connected components after extending a fibre to any separably closed
extension gives the canonical number of geometric connected components. -/
@[stacks 055F "well-definedness", ega "IV 15.5.3" "more general"]
theorem enatCard_connectedComponents_fiberBaseChange (f : X ⟶ Y) (y : Y)
    (K : Type u) [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K] :
    ENat.card (ConnectedComponents (geometricFiber f y K)) =
      numGeometricConnectedComponents f y := by
  unfold numGeometricConnectedComponents
  let K₀ := SeparableClosure (Y.residueField y)
  let Z := f.fiberToSpecResidueField y
  obtain ⟨M, _, _, _, _, _, _⟩ :=
    exists_common_extension (Y.residueField y) K₀ K
  have h (L : Type u) [Field L] [Algebra (Y.residueField y) L] [IsSepClosed L]
      [Algebra L M] [IsScalarTower (Y.residueField y) L M] :
      ENat.card (ConnectedComponents (geometricFiber f y L)) =
        ENat.card (ConnectedComponents (geometricFiber f y M)) := by
    have h₁ := enatCard_connectedComponents_pullback (k := L) (L := M)
      (pullback.snd Z (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) L))))
    have h₂ := enatCard_connectedComponents_pullback_assoc (k := Y.residueField y)
      (L := L) (M := M) Z
    dsimp [geometricFiber, Z] at h₁ h₂ ⊢
    exact h₁.symm.trans h₂
  exact (h K).trans (h K₀).symm

/-- The number of geometric connected components of fibres is preserved by arbitrary base
change. -/
@[stacks 055F "base change"]
theorem numGeometricConnectedComponents_eq_of_isPullback
    {X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X) (g : Y' ⟶ Y)
    (h : IsPullback i f' f g) :
    numGeometricConnectedComponents f' = numGeometricConnectedComponents f ∘ g := by
  funext y'
  let : Algebra (Y.residueField (g y')) (Y'.residueField y') :=
    (g.residueFieldMap y').hom.toAlgebra
  let K := SeparableClosure (Y'.residueField y')
  let : Field K := inferInstance
  let : Algebra (Y'.residueField y') K := inferInstance
  have h₁ := enatCard_connectedComponents_fiberBaseChange f' y' K
  have h₂ := enatCard_connectedComponents_fiberBaseChange f (g y') K
  have hb := enatCard_connectedComponents_fiber_isPullback f f' i g h y' K (by rfl)
  exact h₁.symm.trans (hb.trans h₂)

end AlgebraicGeometry

end

end
