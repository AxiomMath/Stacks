module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitFinitePresentationSite
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus

/-!
# Openness of the flat locus of a morphism

For a morphism of schemes locally of finite presentation, the set of points at which it is flat
is open, and a morphism is flat after restriction to an open subscheme contained in that set.
This is [Stacks, Tag 0399] for the structure sheaf.

Without the finite presentation hypothesis this fails: the pointwise flat locus of a morphism of
schemes need not be open, by
`AlgebraicGeometry.exists_flat_locus_not_open`.

## Main results

* `AlgebraicGeometry.isOpen_setOf_isFlatAt` is openness of the pointwise flat locus.
* `AlgebraicGeometry.flat_of_subset_setOf_isFlatAt`: an open subscheme on which the morphism is
  flat at every point is flat over the target.
* `AlgebraicGeometry.exists_isOpen_flat_of_isFlatAt` combines the two: a point of flatness has
  an open neighbourhood which is flat over the target.

## Implementation notes

`AlgebraicGeometry.IsFlatOverAt` asks the stalk of a module — the stalk of the underlying
presheaf of abelian groups — to be flat over the stalk of the target, while
`AlgebraicGeometry.IsFlatAt` asks the stalk map itself to be a flat ring homomorphism;
`AlgebraicGeometry.isFlatOverAt_unit_iff_isFlatAt` identifies the two for the structure sheaf.

## References

* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 02N3](https://stacks.math.columbia.edu/tag/02N3)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Flatness over a base ring is invariant under a linear equivalence over the bigger ring.**
If `φ : A →+* B` and `G` is a `B`-module linearly equivalent to `B` itself, then `G` is flat
over `A`, for the `A`-action restricted along `φ`, exactly when `φ` is a flat ring
homomorphism. -/
theorem flat_compHom_iff_flat {A B G : Type*} [CommRing A] [CommRing B] [AddCommGroup G]
    [Module B G] (φ : A →+* B) (e : B ≃ₗ[B] G) :
    letI : Module A G := Module.compHom G φ
    (Module.Flat A G ↔ φ.Flat) := by
  let algAB : Algebra A B := φ.toAlgebra
  let moduleAG : Module A G := Module.compHom G φ
  have htowerB : IsScalarTower A B B := IsScalarTower.right
  have htowerG : IsScalarTower A B G := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hcompat : LinearMap.CompatibleSMul B G A B := inferInstance
  let e' : B ≃ₗ[A] G := e.restrictScalars A
  rw [RingHom.Flat]
  exact ⟨fun _ => Module.Flat.of_linearEquiv e', fun _ => Module.Flat.of_linearEquiv e'.symm⟩

/-- Flatness of the structure sheaf over the target at a point, in the sense of
[Stacks, Tag 08KT], is flatness of the morphism at that point, in the sense of
[Stacks, Tag 02N3]. -/
theorem isFlatOverAt_unit_iff_isFlatAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsFlatOverAt f.toLRSHom.toShHom (SheafOfModules.unit X.ringCatSheaf) x ↔
      IsFlatAt f.toLRSHom.toShHom x := by
  have key := flat_compHom_iff_flat (f.stalkMap x).hom
    (Stacks.SheafOfModules.unitStalkLinearEquiv X.toSheafedSpace x)
  rw [Stacks.SheafOfModules.stalkModule_eq] at key
  exact key

/-- **Stacks Project, Tag 0399 for the structure sheaf.** The set of points at which a morphism
locally of finite presentation is flat is open. -/
theorem isOpen_setOf_isFlatAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] :
    IsOpen {x : X | IsFlatAt f.toLRSHom.toShHom x} := by
  simpa only [isFlatOverAt_unit_iff_isFlatAt] using
    isOpen_setOf_flatOverAt f (SheafOfModules.unit X.ringCatSheaf)

/-- A morphism which is flat at every point of an open subscheme of its source is flat after
restriction to that open subscheme. -/
@[stacks 05IM "the flat locus is flat over the base"]
theorem flat_of_subset_setOf_isFlatAt {X S : Scheme.{u}} (f : X ⟶ S) (V : X.Opens)
    (hV : (V : Set X) ⊆ {x : X | IsFlatAt f.toLRSHom.toShHom x}) :
    Flat (V.ι ≫ f) := by
  rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
  intro z
  have hz : IsFlatAt f.toLRSHom.toShHom (V.ι z) := hV z.property
  have hiso : IsIso (V.ι.stalkMap z) := inferInstance
  have hcomp : ((V.ι ≫ f).stalkMap z).hom = (f.stalkMap (V.ι z) ≫ V.ι.stalkMap z).hom :=
    congrArg CommRingCat.Hom.hom (Scheme.Hom.stalkMap_comp V.ι f z)
  rw [hcomp]
  exact (RingHom.Flat.respectsIso.cancel_right_isIso
    (f.stalkMap (V.ι z)) (V.ι.stalkMap z)).mpr hz

/-- A point at which a morphism locally of finite presentation is flat has an open neighbourhood
which is flat over the target. -/
theorem exists_isOpen_flat_of_isFlatAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) (hx : IsFlatAt f.toLRSHom.toShHom x) :
    ∃ V : X.Opens, x ∈ V ∧ Flat (V.ι ≫ f) :=
  ⟨⟨{x : X | IsFlatAt f.toLRSHom.toShHom x}, isOpen_setOf_isFlatAt f⟩, hx,
    flat_of_subset_setOf_isFlatAt f _ le_rfl⟩

end AlgebraicGeometry

end
