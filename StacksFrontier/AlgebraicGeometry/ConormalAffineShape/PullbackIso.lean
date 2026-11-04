module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The module pullback along an isomorphism of schemes is the pushforward along its inverse

The part (2) assertions of [Stacks, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3) compute
the conormal sections over an affine open by comparing them with the affine model
`Spec (R ⧸ I) ⟶ Spec R`, and that comparison arrives as a *pullback along an isomorphism of
schemes*: the identification of the fibre with `Spec (R ⧸ I)` and
`AlgebraicGeometry.IsAffineOpen.isoSpec` both enter the chain that way. The affine model's answer,
on the other hand, is a statement about *sections over an open*. Nothing in the library turned the
one into the other, because a pullback is a left adjoint and its value on sections is not
computable from the definition.

For an isomorphism it is. This file proves

`Scheme.Modules.pullback α.hom ≅ Scheme.Modules.pushforward α.inv`

for `α : A' ≅ A`, and a pushforward *is* computable on sections — `Γ(f_* M, O) = Γ(M, f ⁻¹ᵁ O)`
holds by `rfl` (`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`). So the sections of
`α^* M` over an open `O` of `A'` are the sections of `M` over `α.inv ⁻¹ᵁ O`.

That last `rfl` holds at the level of the underlying abelian groups, `Γ(f_* M, O) = Γ(M, f ⁻¹ᵁ O)`,
and **not** at the level of `ModuleCat`: `((pushforward f).obj M).val.obj (.op O)` is a module over
`Γ(Y, O)` and `M.val.obj (.op (f ⁻¹ᵁ O))` is one over `Γ(X, f ⁻¹ᵁ O)`, so the two are objects of
different categories and the equation does not typecheck there. The
statements below therefore keep the pushforward spelling on the right-hand side, which is the
spelling in which the scalars are the ones the affine identification of Tag 01R3 needs.

## Main definitions

* `Stacks.Conormal.AffineShape.pushforwardEquivalence`: for an isomorphism `α : A' ≅ A` of
  schemes, pushforward along `α.inv` and pushforward along `α.hom` are mutually inverse
  equivalences of the categories of modules.
* `Stacks.Conormal.AffineShape.pullbackIsoPushforwardInv`: **the comparison.** The module pullback
  along `α.hom` is the module pushforward along `α.inv`.
* `Stacks.Conormal.AffineShape.pullbackSectionsIso`: consequently, the sections of `α^* M` over an
  open `O` of `A'` are canonically the sections of `M` over `α.inv ⁻¹ᵁ O`, as modules over
  `Γ(A', O)`.
* `Stacks.Conormal.AffineShape.pullbackTopSectionsIso`: the case `O = ⊤`, which is the one the
  affine model is stated at; `α.inv ⁻¹ᵁ ⊤ = ⊤` holds by `rfl`, so no transport of the open is
  needed there.

## Main results

* `Stacks.Conormal.AffineShape.unit_comp_map_pullbackIsoPushforwardInv`: **the comparison
  commutes with the units.** The unit of `α.hom^* ⊣ α.hom_*` at `M`, followed by `α.hom_*` of the
  comparison, is the unit of the adjunction underlying `pushforwardEquivalence`. Since the
  comparison is `CategoryTheory.Adjunction.leftAdjointUniq`, this is
  `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` and therefore a characterization.
  `StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic` names this factor of
  `Stacks.Conormal.CotangentAppIso.restrictAffineModelIso` as having no unit statement; it now
  has one.

## Route

`AlgebraicGeometry.Scheme.Modules.pushforwardComp` and
`AlgebraicGeometry.Scheme.Modules.pushforwardId` make `pushforward α.inv` and
`pushforward α.hom` mutually inverse, so `CategoryTheory.Equivalence.mk` builds an equivalence
out of them with no coherence obligation of its own. Its `toAdjunction` exhibits
`pushforward α.inv` as a left adjoint of `pushforward α.hom`, and
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` exhibits `pullback α.hom` as
another one, so `CategoryTheory.Adjunction.leftAdjointUniq` identifies them. No property of
schemes is used: the argument is the uniqueness of a left adjoint.

## Universe situation

A single universe `u` (`Scheme.{u}`), which is all `AlgebraicGeometry.Scheme.Modules` offers.

## Transparency gotchas

`CategoryTheory.Equivalence.mk` must be written with its namespace: `Equivalence.mk` resolves to
the `Prop`-valued constructor of an equivalence *relation* even inside `open CategoryTheory`, and
the resulting error is a type mismatch against `∀ x, ?m x x` rather than anything about functors.

`Γ(f_* M, O) = Γ(M, f ⁻¹ᵁ O)` (`AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`) and
`f ⁻¹ᵁ ⊤ = ⊤` are both `rfl`; `W.ι ''ᵁ ⊤ = W` and `W.ι ⁻¹ᵁ W = ⊤` are **not**, which is why the
statements here are about a preimage and never about the image of `⊤`.

## What is not done

* **No clause of [Stacks, Tag 01R3] is discharged and no tag is attached.** This is an input to
  its part (2).
* **Nothing about the conormal sheaf, ideal sheaves or `Ideal.Cotangent`.** The content is the
  comparison of two functors on an arbitrary scheme isomorphism.
* **No statement for a non-invertible morphism.** For a general `f` the pullback is genuinely not
  a pushforward and nothing here applies.
* **No elementwise formula.** `pullbackSectionsIso` is an isomorphism of modules; no description
  of it on a named section is given. `unit_comp_map_pullbackIsoPushforwardInv` relates the
  comparison to the two units, but the *sections* of its right-hand side are not computed, and
  that is a genuine obstruction rather than an omission: `CategoryTheory.Equivalence.mk` replaces
  the unit `pushforwardInvHomIso` it is handed by `CategoryTheory.Equivalence.adjointifyη` of it,
  so the right-hand side is not the composite of `AlgebraicGeometry.Scheme.Modules.pushforwardId`,
  `pushforwardCongr` and `pushforwardComp` that `pushforwardInvHomIso` is built from. Unfolding
  `adjointifyη` and reducing it on sections leaves a goal that **is not type-correct at implicit
  transparency** — the reported mismatch is between `𝟙 Γ(M, O)` and a morphism into
  `Γ(M, (Opens.map (𝟙 A)).obj O)` — so the reduction has to be redone without unfolding, and is
  not done here.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Conormal.AffineShape

variable {A A' : Scheme.{u}} (α : A' ≅ A)

/-- Pushing forward along `α.inv` and then along `α.hom` is the identity. -/
noncomputable def pushforwardInvHomIso : 𝟭 A.Modules ≅
    Scheme.Modules.pushforward α.inv ⋙ Scheme.Modules.pushforward α.hom :=
  (Scheme.Modules.pushforwardComp α.inv α.hom ≪≫
    Scheme.Modules.pushforwardCongr α.inv_hom_id ≪≫ Scheme.Modules.pushforwardId A).symm

/-- Pushing forward along `α.hom` and then along `α.inv` is the identity. -/
noncomputable def pushforwardHomInvIso :
    Scheme.Modules.pushforward α.hom ⋙ Scheme.Modules.pushforward α.inv ≅ 𝟭 A'.Modules :=
  Scheme.Modules.pushforwardComp α.hom α.inv ≪≫
    Scheme.Modules.pushforwardCongr α.hom_inv_id ≪≫ Scheme.Modules.pushforwardId A'

/-- **An isomorphism of schemes induces an equivalence of module categories by pushforward**,
with the pushforward along the inverse as the inverse equivalence. -/
noncomputable def pushforwardEquivalence : A.Modules ≌ A'.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward α.inv)
    (Scheme.Modules.pushforward α.hom) (pushforwardInvHomIso α) (pushforwardHomInvIso α)

/-- **The module pullback along an isomorphism is the module pushforward along its inverse.**

Both functors are left adjoint to `Scheme.Modules.pushforward α.hom`: the pullback by
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, and the pushforward along
`α.inv` because `pushforwardEquivalence` makes the two pushforwards mutually inverse. A left
adjoint is unique up to canonical isomorphism, which is
`CategoryTheory.Adjunction.leftAdjointUniq`. -/
noncomputable def pullbackIsoPushforwardInv :
    Scheme.Modules.pullback α.hom ≅ Scheme.Modules.pushforward α.inv :=
  Adjunction.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction α.hom)
    (pushforwardEquivalence α).toAdjunction

/-- **`pullbackIsoPushforwardInv` commutes with the units.** The unit of
`α.hom^* ⊣ α.hom_*` at `M`, followed by `α.hom_*` of the comparison, is the unit of the adjunction
`α.inv _* ⊣ α.hom _*` underlying `pushforwardEquivalence`.

Both `Scheme.Modules.pullback α.hom` and `Scheme.Modules.pushforward α.inv` are left adjoint to
`Scheme.Modules.pushforward α.hom`, and the comparison is
`CategoryTheory.Adjunction.leftAdjointUniq` of the two adjunctions; so this is
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`, which says the comparison is the unique
morphism carrying one unit to the other, and hence also *characterizes* it.

This is the compatibility with the units that
`StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic` names as absent for this factor of
`Stacks.Conormal.CotangentAppIso.restrictAffineModelIso`.

The right-hand side is **not** `pushforwardInvHomIso α`, even though that is the isomorphism
`pushforwardEquivalence` is built from: `CategoryTheory.Equivalence.mk` discards the given unit in
favour of `CategoryTheory.Equivalence.adjointifyη` of it, so a statement naming
`pushforwardInvHomIso` on the right does not typecheck here. This is also the
reason this factor's *elementwise* description is still missing; see "What is not done". -/
theorem unit_comp_map_pullbackIsoPushforwardInv (M : A.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction α.hom).unit.app M ≫
        (Scheme.Modules.pushforward α.hom).map ((pullbackIsoPushforwardInv α).hom.app M) =
      (pushforwardEquivalence α).toAdjunction.unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

/-- **The sections of a pullback along an isomorphism.** For `α : A' ≅ A`, a module `M` on `A` and
an open `O` of `A'`, the sections of `α^* M` over `O` are the sections of `M` over
`α.inv ⁻¹ᵁ O`, as modules over `Γ(A', O)`.

This is `pullbackIsoPushforwardInv` evaluated at `M` and at `O`; the right-hand side is the
sections of the pushforward along `α.inv`, which are those of `M` over the preimage by `rfl`. -/
noncomputable def pullbackSectionsIso (M : A.Modules) (O : A'.Opens) :
    ((Scheme.Modules.pullback α.hom).obj M).val.obj (.op O) ≅
      ((Scheme.Modules.pushforward α.inv).obj M).val.obj (.op O) :=
  (SheafOfModules.evaluation A'.ringCatSheaf (.op O)).mapIso
    ((pullbackIsoPushforwardInv α).app M)

/-- `pullbackSectionsIso` at `O = ⊤`. Since `α.inv ⁻¹ᵁ ⊤ = ⊤` by `rfl`, the right-hand side is
the global sections of `M` with the scalars of `A'` acting through `α.inv`; this is the shape in
which `Stacks.Conormal.AffineModel.exists_idealSheafΓIsoCotangent` states its answer. -/
noncomputable def pullbackTopSectionsIso (M : A.Modules) :
    ((Scheme.Modules.pullback α.hom).obj M).val.obj (.op ⊤) ≅
      ((Scheme.Modules.pushforward α.inv).obj M).val.obj (.op ⊤) :=
  pullbackSectionsIso α M ⊤

end Stacks.Conormal.AffineShape

end
