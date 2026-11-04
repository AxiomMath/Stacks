module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Global sections pulled back, and the pseudofunctoriality of the inverse image

A global section of a sheaf of modules `M` on `Y` has a canonical image in the global sections of
`f^*M` for a morphism `f : X ⟶ Y`: the unit of the pullback--pushforward adjunction, read over
`⊤`, since `f ⁻¹ᵁ ⊤` and `⊤` are definitionally equal. This file names that operation and proves
how it interacts with the four structural isomorphisms of the inverse image — the identity, a
composite, two equal morphisms, and a morphism of the module being pulled back.

Those four facts are what a computation along a *composite* of pullbacks needs. The
pseudofunctoriality isomorphisms `AlgebraicGeometry.Scheme.Modules.pullbackId`,
`pullbackComp` and `pullbackCongr` are isomorphisms of *functors*, with no description on
sections; without the lemmas below a global section cannot be followed through them at all.

## Main definitions

* `Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection`: the image of a global section under
  the unit of the pullback--pushforward adjunction.

## Main results

* `Stacks.AlgebraicGeometry.PullbackUnit.pullback_map_pullbackSection`: naturality — the pullback
  of a morphism carries the pulled-back section to the pulled-back image.
* `Stacks.AlgebraicGeometry.PullbackUnit.pullbackId_hom_pullbackSection`: the identification of
  the pullback along the identity with the identity functor undoes the operation.
* `Stacks.AlgebraicGeometry.PullbackUnit.pullbackComp_inv_pullbackSection` and
  `pullbackComp_hom_pullbackSection`: the operation for a composite is the operation for the two
  factors, in both directions across the pseudofunctoriality isomorphism.
* `Stacks.AlgebraicGeometry.PullbackUnit.pullbackCongr_hom_pullbackSection` and
  `pullbackCongr_inv_pullbackSection`: the operation does not see which of two equal morphisms it
  is formed with.

## The route

Three of the four are the *same* Mathlib lemma, `CategoryTheory.unit_conjugateEquiv`, read at the
two coherences Mathlib already supplies for the inverse image:
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom` and
`conjugateEquiv_pullbackComp_inv`. `CategoryTheory.conjugateEquiv` is the bijection between
natural transformations of left adjoints and of right adjoints, and `unit_conjugateEquiv` is
exactly the statement that the units agree across it. Taking components at `⊤` turns each into a
statement about sections, because the matching pushforward isomorphisms
`AlgebraicGeometry.Scheme.Modules.pushforwardId` and `pushforwardComp` are the *identity* on
sections (`pushforwardId_inv_app_app`, `pushforwardComp_hom_app_app`, both `rfl`). The composite
adjunction's unit is unfolded by `CategoryTheory.Adjunction.comp_unit_app`.

Naturality is `CategoryTheory.NatTrans.naturality` of the unit, transported onto a section.
Congruence is `subst` on the equality of morphisms, after which
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` is `CategoryTheory.eqToIso` of a reflexivity
proof and both directions are the identity.

The `hom` direction for a composite is the `inv` direction cancelled, which needs an
isomorphism of *functors* to cancel at a component rather than an isomorphism of objects: see
the implementation note.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` and every equality of morphisms here is transported
onto a section by `congrArg` of a function that evaluates a morphism, never by `rw`.

`Stacks.AlgebraicGeometry.PullbackUnit.natIso_hom_inv_app` cancels a natural isomorphism at a
component *without* forming `CategoryTheory.Iso.app`. That is deliberate.
`AlgebraicGeometry.Scheme.Modules.pullback` is a left adjoint obtained by a choice principle, so
reducing it is hopeless, and `CategoryTheory.Iso.app_hom` on a component of `pullbackComp`
exhausts the kernel's budget, as recorded in
`StacksFrontier/AlgebraicGeometry/ProjInclusionTwist/Basic.lean`.
Cancelling at the level of the natural isomorphism keeps the component opaque.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.PullbackUnit

universe u

variable {X Y Z : Scheme.{u}}

/-- A natural isomorphism of functors landing in sheaves of modules on a scheme cancels on
sections, at a component. Stated for the natural isomorphism rather than for
`CategoryTheory.Iso.app` of it: forming the component as an isomorphism of objects requires
`CategoryTheory.Iso.app_hom`, which for a component of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` exhausts the kernel's budget. -/
public theorem natIso_hom_inv_app {C : Type*} [Category C] {W : Scheme.{u}}
    {F G : C ⥤ W.Modules} (ε : F ≅ G) (c : C) (V : W.Opens) (x : (G.obj c).val.obj (op V)) :
    (ε.hom.app c).val.app (op V) ((ε.inv.app c).val.app (op V) x) = x :=
  congrArg (fun ρ : G ⟶ G => (ρ.app c).val.app (op V) x) ε.inv_hom_id

/-- Equal morphisms of sheaves of modules agree on a global section. -/
private theorem app_top_congr {W : Scheme.{u}} {M N : W.Modules} {ρ σ : M ⟶ N} (h : ρ = σ)
    (s : M.val.obj (op ⊤)) : ρ.val.app (op ⊤) s = σ.val.app (op ⊤) s :=
  congrArg (fun ρ : M ⟶ N => ρ.val.app (op ⊤) s) h

/-- **A global section pulled back.** The image of a global section of `M` in the global sections
of `f^*M`, under the unit of the pullback--pushforward adjunction. The two sides typecheck
against each other because `f ⁻¹ᵁ ⊤` and `⊤` are definitionally equal. -/
public def pullbackSection (f : X ⟶ Y) (M : Y.Modules) (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullback f).obj M).val.obj (op ⊤) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤) s

/-- **Naturality.** The pullback of a morphism carries the pulled-back section to the pulled-back
image. This is naturality of the unit of the adjunction, read over `⊤`. -/
public theorem pullback_map_pullbackSection (f : X ⟶ Y) {M N : Y.Modules} (φ : M ⟶ N)
    (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullback f).map φ).val.app (op ⊤) (pullbackSection f M s) =
      pullbackSection f N (φ.val.app (op ⊤) s) :=
  app_top_congr ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ).symm s

/-- **Congruence, forwards.** The identification of the pullbacks along two equal morphisms
carries the section pulled back along one to the section pulled back along the other. -/
public theorem pullbackCongr_hom_pullbackSection {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules)
    (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullbackCongr hf).hom.app M).val.app (op ⊤) (pullbackSection f M s) =
      pullbackSection g M s := by
  subst hf
  rfl

/-- **Congruence, backwards.** -/
public theorem pullbackCongr_inv_pullbackSection {f g : X ⟶ Y} (hf : f = g) (M : Y.Modules)
    (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullbackCongr hf).inv.app M).val.app (op ⊤) (pullbackSection g M s) =
      pullbackSection f M s := by
  subst hf
  rfl

/-- **The identity.** Pulling a global section back along the identity and undoing the
identification of that pullback with the identity functor returns the section.

This is `CategoryTheory.unit_conjugateEquiv` at
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom`: the conjugate of
`pullbackId`'s `hom` is `pushforwardId`'s `inv`, which is the identity on sections. -/
public theorem pullbackId_hom_pullbackSection (W : Scheme.{u}) (M : W.Modules)
    (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullbackId W).hom.app M).val.app (op ⊤) (pullbackSection (𝟙 W) M s) = s := by
  have h := unit_conjugateEquiv (Adjunction.id)
    (Scheme.Modules.pullbackPushforwardAdjunction (𝟙 W))
    (Scheme.Modules.pullbackId W).hom M
  rw [Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact (app_top_congr h s).symm

/-- **Composition, backwards.** The section pulled back along a composite, carried across the
pseudofunctoriality isomorphism, is the section pulled back along the second factor and then
along the first.

This is `CategoryTheory.unit_conjugateEquiv` at
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`: the conjugate of
`pullbackComp`'s `inv` is `pushforwardComp`'s `hom`, which is the identity on sections, and the
composite adjunction's unit is the composite of the two units
(`CategoryTheory.Adjunction.comp_unit_app`). -/
public theorem pullbackComp_inv_pullbackSection (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).val.app (op ⊤)
        (pullbackSection (f ≫ g) M s) =
      pullbackSection f ((Scheme.Modules.pullback g).obj M) (pullbackSection g M s) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  exact (app_top_congr h s).symm

/-- **Composition, forwards.** The same identity read in the other direction, obtained by
cancelling the pseudofunctoriality isomorphism at the component. -/
public theorem pullbackComp_hom_pullbackSection (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (s : M.val.obj (op ⊤)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).val.app (op ⊤)
        (pullbackSection f ((Scheme.Modules.pullback g).obj M) (pullbackSection g M s)) =
      pullbackSection (f ≫ g) M s :=
  (congrArg (((Scheme.Modules.pullbackComp f g).hom.app M).val.app (op ⊤))
      (pullbackComp_inv_pullbackSection f g M s).symm).trans
    (natIso_hom_inv_app (Scheme.Modules.pullbackComp f g) M ⊤ _)

end Stacks.AlgebraicGeometry.PullbackUnit

end
