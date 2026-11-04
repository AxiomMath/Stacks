module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangePasting

/-!
# The derived base change map of the degenerate square is the derived unit

For a morphism of ringed spaces `p : Z ⟶ X` the square

```
Z --p--> X
|p       |𝟙
X --𝟙--> X
```

commutes on the nose, and the derived base change map of [Stacks, Tag 08HY] attached to it is a
map `L(𝟙)^* (R(𝟙)_* K) ⟶ Rp_* (Lp^* K)`. This file proves that it is the **derived unit** of
`Lp^* ⊣ Rp_*` of [Stacks, Tag 079W], read through the two identity isomorphisms
`L(𝟙)^* ≅ 𝟭` and `R(𝟙)_* ≅ 𝟭` of `Stacks.Cohomology.DerivedPushforwardAssociativity`.

This is the degenerate case the pasting law of [Stacks, Tag 0ATL] needs in order to compute the
adjoint transpose, under `Lg^* ⊣ Rg_*`, of the derived base change map of an arbitrary
commutative square: pasting a square on top of this one replaces the base change map by its
transpose, and the transpose is what a statement about the *sections* of the base change map
sees.

## Main results

All in the namespace `Stacks.Cohomology.DerivedBaseChange`.

* `derivedAdjunction_id_counit_app`: the derived counit of the identity is the composite of the
  two identity isomorphisms.
* `derivedAdjunction_homEquiv_symm_comp_unit`: transposing a composite whose last factor is the
  derived unit deletes that factor.
* `derivedAdjunction_homEquiv_symm_idIso_comp_unit`: the transpose of the composite of the two
  identity isomorphisms with the derived unit.
* `derivedPullbackCompIsoLeft_self_id_hom_app`: at the degenerate square the transport carried by
  `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` is the identity.
* `derivedBaseChangeMap_self_id`: **the derived base change map of the degenerate square is the
  derived unit.**

## Implementation notes

*Every step is its own declaration, and that is forced.* The heartbeat budget is counted per
declaration, and in this cube each of `derivedBaseChangeMap_adjoint`, the transposition of the
composite with the unit, and the identification of the counit of the identity costs a
substantial fraction of it on its own. Assembled as `have`s inside one proof the three together
exceed 200000 heartbeats and the declaration fails with `(deterministic) timeout at whnf`, even
though each step checks in seconds in isolation. Raising `maxHeartbeats` is not a
way to finish; splitting is.

*`Category.assoc` backwards is not affordable here, and does not have to be used.* Rewriting
with `← Category.assoc` to turn `x ≫ y ≫ unit` into `(x ≫ y) ≫ unit` is a
`(deterministic) timeout at isDefEq` at this spelling: the motive abstracts a composite of
morphisms of the unbounded derived category of module sheaves. The cure is to state
`derivedAdjunction_homEquiv_symm_comp_unit` at the **two** factors `x` and `y` separately, in the
right-associated form the consumer already has, so that no reassociation is needed at the
application site.

*The last step is `Eq.trans` and not `rw`.* Rewriting the goal with
`derivedAdjunction_homEquiv_symm_idIso_comp_unit` forms a motive over the transposed composite
and times out; `refine Eq.trans ?_ (…).symm` forms none, and the remaining goal is the
cancellation of one composition isomorphism against its inverse.

*No `stacks` attribute is placed.* Nothing here is a conclusion of a tag: the degenerate case of
[Stacks, Tag 08HY]'s base change map is a step inside the computation of its transpose.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0ATL](https://stacks.math.columbia.edu/tag/0ATL)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPushforwardAssociativity

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

section DegenerateSquare

variable {X Z : RingedSpace.{u, u}} (p : Z ⟶ X)

/-- The derived counit of the identity, read through the two identity isomorphisms. -/
theorem derivedAdjunction_id_counit_app (X : RingedSpace.{u, u})
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedAdjunction (𝟙 X)).counit.app K =
      (derivedPullbackIdIso X).hom.app ((derivedPushforward (𝟙 X)).obj K) ≫
        (derivedPushforwardIdIso X).hom.app K := by
  rw [derivedPullbackIdIso, Adjunction.leftAdjointIdIso_hom_app]
  have h1 : (derivedPushforwardIdIso X).inv.app ((derivedPushforward (𝟙 X)).obj K) ≫
      (derivedPushforward (𝟙 X)).map ((derivedPushforwardIdIso X).hom.app K) = 𝟙 _ := by
    have hn := (derivedPushforwardIdIso X).inv.naturality
      ((derivedPushforwardIdIso X).hom.app K)
    simp only [Functor.id_map] at hn
    rw [← hn]
    simp
  have hc := (derivedAdjunction (𝟙 X)).counit_naturality ((derivedPushforwardIdIso X).hom.app K)
  rw [Category.assoc, ← hc, ← Category.assoc, ← Functor.map_comp, h1]
  simp

/-- Transposing a composite whose last factor is the derived unit of `Lp^* ⊣ Rp_*` deletes that
factor: the transpose is the derived pullback of the rest. -/
theorem derivedAdjunction_homEquiv_symm_comp_unit
    {A B K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (x : A ⟶ B)
    (y : B ⟶ K) :
    ((derivedAdjunction p).homEquiv A ((derivedPullback p).obj K)).symm
        (x ≫ y ≫ (derivedAdjunction p).unit.app K) = (derivedPullback p).map (x ≫ y) := by
  rw [Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc, Adjunction.left_triangle_components,
    Category.comp_id]

/-- The transpose, under `Lp^* ⊣ Rp_*`, of the composite of the two identity isomorphisms with
the derived unit: it is the derived pullback along `p` of the derived counit of the identity. -/
theorem derivedAdjunction_homEquiv_symm_idIso_comp_unit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((derivedAdjunction p).homEquiv
        ((derivedPullback (𝟙 X)).obj ((derivedPushforward (𝟙 X)).obj K))
        ((derivedPullback p).obj K)).symm
        ((derivedPullbackIdIso X).hom.app ((derivedPushforward (𝟙 X)).obj K) ≫
          (derivedPushforwardIdIso X).hom.app K ≫ (derivedAdjunction p).unit.app K) =
      (derivedPullback p).map ((derivedAdjunction (𝟙 X)).counit.app K) := by
  rw [derivedAdjunction_id_counit_app, derivedAdjunction_homEquiv_symm_comp_unit]

/-- For the square `p ≫ 𝟙 = p ≫ 𝟙` the transport carried by
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` is the identity, so that
isomorphism is the composition isomorphism of [Stacks, Tag 0D5S] itself. -/
theorem derivedPullbackCompIsoLeft_self_id_hom_app
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedPullbackCompIsoLeft p p (𝟙 X) (𝟙 X) rfl).hom.app M =
      (derivedPullbackCompIsoCanonical p (𝟙 X)).hom.app M := by
  simp [derivedPullbackCompIsoLeft]

/-- **The derived base change map of the square `p ≫ 𝟙 = p ≫ 𝟙` is the derived unit** of
`Lp^* ⊣ Rp_*`, read through the two identity isomorphisms `L(𝟙)^* ≅ 𝟭` and `R(𝟙)_* ≅ 𝟭`. -/
theorem derivedBaseChangeMap_self_id
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    derivedBaseChangeMap p p (𝟙 X) (𝟙 X) rfl K =
      (derivedPullbackIdIso X).hom.app ((derivedPushforward (𝟙 X)).obj K) ≫
        (derivedPushforwardIdIso X).hom.app K ≫ (derivedAdjunction p).unit.app K := by
  refine ((derivedAdjunction p).homEquiv
    ((derivedPullback (𝟙 X)).obj ((derivedPushforward (𝟙 X)).obj K))
    ((derivedPullback p).obj K)).symm.injective ?_
  refine Eq.trans ?_ (derivedAdjunction_homEquiv_symm_idIso_comp_unit p K).symm
  rw [derivedBaseChangeMap_adjoint, derivedPullbackCompIsoLeft_self_id_hom_app,
    ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end DegenerateSquare

end Stacks.Cohomology.DerivedBaseChange

end
