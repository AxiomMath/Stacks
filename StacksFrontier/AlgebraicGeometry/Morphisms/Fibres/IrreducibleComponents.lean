module

public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.RingTheory.GeometricallyIrreducible.IrreducibleComponents
public import StacksCore.Tactic.StacksAttribute

/-!
# Irreducible components of the fibres of a morphism of schemes

For a morphism of schemes, the number of irreducible components of a geometric fibre is
independent of the chosen separably closed extension of the residue field, and both this count
and the locus of geometrically irreducible fibres are unchanged by arbitrary base change.

## Main definitions

* `AlgebraicGeometry.geometricFiber`: the base change of a scheme-theoretic fibre to a field
  extension of its residue field.
* `AlgebraicGeometry.geometricIrreducibleComponentCount`: the extended-natural-valued function
  counting the irreducible components of the geometric fibres.

## Main results

* `AlgebraicGeometry.geometricallyIrreducibleFiberLocus_baseChange`: the points with
  geometrically irreducible fibre pull back exactly under an arbitrary base change.
* `AlgebraicGeometry.encard_irreducibleComponents_geometricFiber`: any separably closed
  extension computes the geometric irreducible-component count.
* `AlgebraicGeometry.geometricIrreducibleComponentCount_pullback`: the count is preserved by
  base change.

## Implementation notes

The base change of `f` along `g` is represented by the canonical pullback projection
`pullback.snd f g`. A fibre is geometrically irreducible precisely when its structure morphism
to the spectrum of the residue field has Mathlib's `GeometricallyIrreducible` property.

`geometricIrreducibleComponentCount` is defined using a separable closure of each residue field.
Its well-definedness is expressed by `encard_irreducibleComponents_geometricFiber`, which
compares that value with the count over any separably closed extension. A geometric fibre over
an extension field is represented by the corresponding pullback of the scheme-theoretic fibre.

## References

* [Stacks Project, Tag 0555](https://stacks.math.columbia.edu/tag/0555)
* [Stacks Project, Tag 0556](https://stacks.math.columbia.edu/tag/0556)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

private lemma encard_irreducibleComponents_eq_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (irreducibleComponents X).encard = (irreducibleComponents Y).encard := by
  let h := Scheme.homeoOfIso e
  exact Set.encard_congr (Equiv.symm
    (irreducibleComponentsEquivOfIsPreirreducibleFiber h h.continuous h.isOpenMap
      (fun y => (Set.subsingleton_singleton.preimage h.injective).isPreirreducible)
      h.surjective).toEquiv)

/-- The geometric fibre of `f` at `y`, formed using an extension field `K` of the residue
field `κ(y)`. -/
def geometricFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (K : Type u)
    [Field K] [Algebra (Y.residueField y) K] : Scheme.{u} :=
  pullback (f.fiberToSpecResidueField y)
    (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)))

private lemma encard_geometricFiber_eq_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (K : Type u)
    [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K] :
    (irreducibleComponents (geometricFiber f y K)).encard =
      (irreducibleComponents
        (geometricFiber f y (SeparableClosure (Y.residueField y)))).encard := by
  let k := Y.residueField y
  let ks := SeparableClosure k
  let : Algebra ks K := (IsSepClosed.lift : ks →ₐ[k] K).toRingHom.toAlgebra
  let a := pullbackRightPullbackFstIso
    (Spec.map (CommRingCat.ofHom (algebraMap k ks)))
    (f.fiberToSpecResidueField y)
    (Spec.map (CommRingCat.ofHom (algebraMap ks K)))
  let e₂ : pullback
      (Spec.map (CommRingCat.ofHom (algebraMap ks K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k ks)))
      (f.fiberToSpecResidueField y) ≅ geometricFiber f y K :=
    pullback.congrHom (by
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← IsScalarTower.algebraMap_eq]
      rfl) rfl ≪≫ pullbackSymmetry _ _
  let e : geometricFiber f y K ≅
      pullback (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k ks)))
        (f.fiberToSpecResidueField y))
        (Spec.map (CommRingCat.ofHom (algebraMap ks K))) :=
    e₂.symm ≪≫ a.symm ≪≫ pullbackSymmetry _ _
  rw [encard_irreducibleComponents_eq_of_iso e,
    Set.encard_congr (bijOn_irreducibleComponents_baseChange_of_isSepClosed
      ks K (pullback (Spec.map (CommRingCat.ofHom (algebraMap k ks)))
        (f.fiberToSpecResidueField y))
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k ks)))
        (f.fiberToSpecResidueField y))).equiv]
  exact encard_irreducibleComponents_eq_of_iso
    (pullbackSymmetry (Spec.map (CommRingCat.ofHom (algebraMap k ks)))
      (f.fiberToSpecResidueField y))

/-- The number, as an extended natural number, of geometrically irreducible components of each
fibre of a morphism of schemes. -/
@[stacks 0556 "the function", ega "IV 4.5.2" "more general", ega "IV 4.7.4" "more general"]
def geometricIrreducibleComponentCount {X Y : Scheme.{u}} (f : X ⟶ Y) : Y → ℕ∞ := fun y ↦
  (irreducibleComponents
    (geometricFiber f y (SeparableClosure (Y.residueField y)))).encard

/-- The number of irreducible components of the geometric fibre can be computed after extension
to any separably closed field containing the residue field. -/
@[stacks 0556 "well-definedness", ega "IV 4.5.1" "partial"]
theorem encard_irreducibleComponents_geometricFiber {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) (K : Type u) [Field K] [Algebra (Y.residueField y) K] [IsSepClosed K] :
    (irreducibleComponents (geometricFiber f y K)).encard =
      geometricIrreducibleComponentCount f y := encard_geometricFiber_eq_fiber f y K

private lemma encard_geometricFiber_pullback_sameField {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (y : Y') (K : Type u)
    [Field K] [Algebra (Y'.residueField y) K]
    [Algebra (Y.residueField (g y)) K]
    (compat : (algebraMap (Y'.residueField y) K).comp (g.residueFieldMap y).hom =
      algebraMap (Y.residueField (g y)) K)
    [IsSepClosed K] :
    (irreducibleComponents (geometricFiber (pullback.snd f g) y K)).encard =
      (irreducibleComponents (geometricFiber f (g y) K)).encard := by
  have h := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) y
  have q := IsPullback.of_hasPullback
    ((pullback.snd f g).fiberToSpecResidueField y)
    (Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y) K)))
  have canonical := IsPullback.of_hasPullback
    (f.fiberToSpecResidueField (g y))
    ((Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y) K))) ≫
      Spec.map (g.residueFieldMap y))
  let e₁ := (q.paste_horiz h).isoIsPullback _ _ canonical
  let e₂ : pullback (f.fiberToSpecResidueField (g y))
      ((Spec.map (CommRingCat.ofHom (algebraMap (Y'.residueField y) K))) ≫
        Spec.map (g.residueFieldMap y)) ≅ geometricFiber f (g y) K :=
    pullback.congrHom rfl (by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact DFunLike.congr_fun compat x)
  exact encard_irreducibleComponents_eq_of_iso (e₁ ≪≫ e₂)

/-- Formation of the function counting geometrically irreducible components of fibres commutes
with arbitrary base change. -/
@[stacks 0556 "base change"]
theorem geometricIrreducibleComponentCount_pullback {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) :
    geometricIrreducibleComponentCount (pullback.snd f g) =
      geometricIrreducibleComponentCount f ∘ g := by
  funext y'
  simp only [geometricIrreducibleComponentCount, Function.comp_apply]
  let : Algebra (Y.residueField (g y')) (SeparableClosure (Y'.residueField y')) :=
    ((algebraMap (Y'.residueField y') (SeparableClosure (Y'.residueField y'))).comp
      (g.residueFieldMap y').hom).toAlgebra
  rw [encard_geometricFiber_pullback_sameField f g y'
    (SeparableClosure (Y'.residueField y')) (by rfl)]
  exact encard_geometricFiber_eq_fiber f (g y')
    (SeparableClosure (Y'.residueField y'))

/-- Geometric irreducibility of the fibre at `y'` is detected after any cartesian square. -/
private theorem geometricallyIrreducible_fiberToSpecResidueField_iff_of_isPullback
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {i : X' ⟶ X} {g : Y' ⟶ Y}
    (h : IsPullback i f' f g) (y' : Y') :
    GeometricallyIrreducible (f'.fiberToSpecResidueField y') ↔
      GeometricallyIrreducible (f.fiberToSpecResidueField (g y')) := by
  let : Algebra (Y.residueField (g y')) (Y'.residueField y') :=
    (g.residueFieldMap y').hom.toAlgebra
  have hp := isPullback_fiberToSpecResidueField_of_isPullback h y'
  have he : IsPullback hp.isoPullback.inv
      (pullback.snd (f.fiberToSpecResidueField (g y')) (Spec.map (g.residueFieldMap y')))
      (f'.fiberToSpecResidueField y') (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨hp.isoPullback_inv_snd.trans (Category.comp_id _).symm⟩
  exact ⟨fun hf => (geometricallyIrreducible_iff_baseChange_fieldExtension
    (Y.residueField (g y')) (Y'.residueField y')
    (f.fiberToSpecResidueField (g y'))).mpr (MorphismProperty.of_isPullback he hf),
    fun hf => MorphismProperty.of_isPullback hp hf⟩

/-- **Stacks Project, Tag 0555.** The points with geometrically irreducible fibre pull back
exactly under an arbitrary base change. -/
@[stacks 0555 "the locus pulls back under the chosen fibre product"]
theorem geometricallyIrreducibleFiberLocus_baseChange
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    {y' : Y' | GeometricallyIrreducible
      ((pullback.snd f g).fiberToSpecResidueField y')} =
      g ⁻¹' {y : Y | GeometricallyIrreducible (f.fiberToSpecResidueField y)} := by
  ext y'
  exact geometricallyIrreducible_fiberToSpecResidueField_iff_of_isPullback
    (IsPullback.of_hasPullback f g) y'

/-- **Stacks Project, Tag 0555.** The points with geometrically irreducible fibre pull back
exactly under an arbitrary cartesian square, not only under the chosen fibre product. -/
@[stacks 0555 "the locus pulls back under an arbitrary cartesian square"]
theorem geometricallyIrreducibleFiberLocus_eq_preimage_of_isPullback
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (i : X' ⟶ X) (g : Y' ⟶ Y)
    (h : IsPullback i f' f g) :
    {y' : Y' | GeometricallyIrreducible (f'.fiberToSpecResidueField y')} =
      g ⁻¹' {y : Y | GeometricallyIrreducible (f.fiberToSpecResidueField y)} := by
  ext y'
  exact geometricallyIrreducible_fiberToSpecResidueField_iff_of_isPullback h y'

end AlgebraicGeometry

end

end
