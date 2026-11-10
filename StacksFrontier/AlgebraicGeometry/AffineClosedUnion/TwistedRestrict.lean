module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.TwistedUnit

/-!
# The twisted restriction legs are restriction of sections

`StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.TwistedSections` builds the twisted square

```
Γ(L, V) --------------> Γ(i₁^*L, i₁⁻¹V)
   |                         |
   v                         v
Γ(i₂^*L, i₂⁻¹V) -----> Γ((i₁⊔i₂)^*L, (i₁⊔i₂)⁻¹V)
```

out of two kinds of leg: `Stacks.AffineClosedUnion.twistedUnit`, the twist by `L` of the
comparison `𝒪_X ⟶ i_*𝒪_Z`, and `Stacks.AffineClosedUnion.twistedRestrict`, the twist of the
restriction `i_*𝒪_Z ⟶ k_*𝒪_W` along a factorisation `k = g ≫ i`.  The sibling file
`StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.TwistedUnit` identifies the first with the
unit of `i^* ⊣ i_*`; this file identifies the second, which is the remaining obligation that file
recorded, and with it every leg of the twisted square is a canonical map a consumer can read as
restriction of sections.

## The route, and why it is not the mirror of the one for `twistedUnit`

`twistedRestrict` is defined with the projection-formula isomorphism at `i` on the **left and
inverted**, so the transpose trick that computes `twistedUnit` does not apply unchanged: there is
no morphism out of a tensor product to feed to the adjunction.  **One rewrite removes the
inverse**: `CategoryTheory.Iso.inv_comp_eq` turns the goal into

`(- ⊗ L)(i_*𝒪_Z ⟶ k_*𝒪_W) ≫ P_k = P_i ≫ ρ`,

with both projection-formula isomorphisms in the forward direction, and *both sides are now
morphisms out of the sheaf tensor product* `i_*𝒪_Z ⊗ L`.  So the square can be checked on the
sheafification-unit images of pure tensors, and the whole computation becomes an identity of
sections.  No inverse form of the projection formula is declared, and none is needed; the
dispatch's estimate that one would be is corrected below.

What makes the element-level route work is one new input, which is a statement about the
projection formula that this repository did not have:

* `Stacks.AffineProjectionFormula.projectionFormulaMap_app_unit_tmul`: **the projection-formula
  map on sections.** It carries the sheafification-unit image of `a ⊗ y`, with `a` a section of
  `f_*𝒢` over `U` and `y` a section of `ℋ`, to the unit image of `a ⊗ η y` over `f⁻¹U`, where
  `η` is the unit of `f^* ⊣ f_*`.  The counit factor in the definition of the map disappears
  because the right triangle of the adjunction makes it undo the unit on sections of a
  pushforward — that is
  `Stacks.AffineProjectionFormula.counit_app_pullbackUnit`.  Composing with the left unit
  constraint on `Z` turns this into `a • η y`, which is the form the twist consumes.

With that, both sides of the square above come down, on `x ⊗ y`, to a scalar multiple of the
restriction of `y`: on the left the scalar is the comorphism image `g^♯x` produced by the
restriction leg, on the right it is produced by the semilinearity of the unit of `g^* ⊣ g_*`.
The two agree, and the restriction of the restriction of `y` is the restriction of `y` — which is
the **mate identity**: the unit of the composite adjunction `(g^* ⊣ g_*) ∘ (i^* ⊣ i_*)`,
transported along `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pushforwardComp`, is the unit of `(g ≫ i)^* ⊣ (g ≫ i)_*`.  That
is Mathlib's `CategoryTheory.unit_conjugateEquiv` applied to
`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`, and it is the only
non-elementary ingredient of `Stacks.AffineClosedUnion.unit_comp_unitRestrict`.

## Implementation notes

**The transitivity of the projection formula is not needed and is not proved.**  The obvious
route — write the restriction leg as `i_*` of the unit of `g^* ⊣ g_*` and push the projection
formula at `k` through as the composite of the formulas at `i` and at `g` — needs that
transitivity, which in turn needs a composition law for the pullback tensor comparison of
[Stacks, Tag 01CD].  The element-level route above avoids both.

**`AlgebraicGeometry.Scheme.Modules.pushforwardComp` is the identity on sections** (Mathlib's
`pushforwardComp_hom_app_app`), which is why `Stacks.AffineClosedUnion.unitRestrict_app_apply`
is `rfl`: the canonical restriction leg of this file is, on sections, literally the unit of
`g^* ⊣ g_*` followed by the pullback-composition comparison.

**One declared return type is load-bearing.**  The module structure on the
sections of a sheaf of modules is keyed at its sheaf of rings, and
`AlgebraicGeometry.Scheme.Modules X` is `SheafOfModules X.ringCatSheaf` while every lemma used
here is stated over `Stacks.RingedSpace.structureRingSheaf X.toRingedSpace`.  The two are
definitionally equal and **not interchangeable for instance resolution**: with
`(AlgebraicGeometry.Scheme.Modules.pullbackComp g i).hom.app L` written out, `map_smul` dies with
`synthInstanceFailed` on `SMul _ ((Scheme.Modules.pullback i ⋙ Scheme.Modules.pullback g).obj
L).val.obj _`.  `Stacks.AffineClosedUnion.pullbackCompHom` is that same morphism with its type
declared at the `Stacks.RingedSpace.pullbackFunctor` spelling, after which the instance is found.
Without it, two `synthInstanceFailed` errors arise.

**The twist and the uncurried tensor bifunctor differ by a functor identity, not by
conversion.**  `Stacks.AffineClosedUnion.twistFunctor X L` is
`Stacks.SheafOfModules.Tensor.sheafTensor` flipped at `L`, so `(twistFunctor X L).map φ` is
`((sheafTensor).map φ).app L`; the section-level lemma
`Stacks.RingedSpace.tensorSheaf_map_unit_tmul` is stated for the uncurried bifunctor at
`φ ×ₘ 𝟙 L`, which carries the extra factor `((sheafTensor).obj _).map (𝟙 L)`.  The two agree by
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`, whose proof is a `Functor.map_comp` and
not a `rfl`, so `twistedRestrict_eq_unitRestrict` crosses once and at the morphism level, before
descending to sections — as `Stacks.AffineClosedUnion.twistedUnit_eq_unit` does in the sibling
file.  Everything after the crossing is stated for the uncurried bifunctor.

**The two scalars are carried as free variables named by equations**
(`Stacks.AffineProjectionFormula.projectionFormulaMap_structureUnitor_app_unit_tmul` and
`Stacks.AffineClosedUnion.unitRestrict_app_smul_pullbackUnit`), as in the sibling file: the twist
produces them as closed terms at a spelling a rewrite cannot locate, and binding them in the
statement applies the lemma without one.

## Main definitions

* `Stacks.AffineClosedUnion.pullbackCompHom`: the pullback-composition comparison
  `g^*(i^*L) ⟶ (g ≫ i)^*L`, with its codomain declared at the ringed-space spelling.
* `Stacks.AffineClosedUnion.unitRestrict`: **the canonical restriction leg**
  `i_*(i^*L) ⟶ (g ≫ i)_*((g ≫ i)^*L)`, namely `i_*` of the unit of `g^* ⊣ g_*` conjugated by the
  composition isomorphisms.

## Main results

* `Stacks.AffineProjectionFormula.projectionFormulaMap_app_unit_tmul`: **the projection-formula
  map on sections**, for an arbitrary morphism of ringed spaces, and
  `projectionFormulaMap_structureUnitor_app_unit_tmul` its composite with the left unit
  constraint, which is the twisted comparison `f_*𝒪_Z ⊗ L ⟶ f_*(f^*L)`.
* `Stacks.AffineClosedUnion.unit_comp_unitRestrict`: the unit of `i^* ⊣ i_*` followed by the
  canonical restriction leg is the unit of `(g ≫ i)^* ⊣ (g ≫ i)_*`.
* `Stacks.AffineClosedUnion.twistedRestrict_eq_unitRestrict`: **the obligation
  `TwistedSections` recorded.** `twistedRestrict` is the canonical restriction leg.
* `Stacks.AffineClosedUnion.twistedRestrict_app_unit_app`: consequently, over any open, it
  carries the restriction of a section of `L` to its restriction.
* `Stacks.AffineClosedUnion.existsUnique_unit_app_eq_zero_of_unitRestrict_eq_zero`: the vanishing
  form of the twisted square with **every** leg a canonical map — the form a consumer of
  [Stacks, Tag 09NX] can use.

No `@[stacks]` attribute is attached to anything here, for the reason the two sibling files give:
the twisted square is the statement of no tag, and this is a coherence internal to its
construction.  [Stacks, Tag 09NX] is the ampleness criterion, whose own declaration is not proved
here.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open PresheafOfModules (Hom)
open scoped TensorProduct
open scoped CategoryTheory.Prod

universe u

namespace Stacks.AffineProjectionFormula

section RingedSpace

variable {Z X : RingedSpace.{u, u}} (f : Z ⟶ X)

/-- Equal morphisms of sheaves of modules agree on sections. -/
private theorem hom_app_val_congr {R : Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u}}
    {A B : SheafOfModules.{u} R} {h₁ h₂ : A ⟶ B} (h : h₁ = h₂) (U : (Opens X.carrier)ᵒᵖ)
    (x : ToType (A.val.obj U)) : Hom.app h₁.val U x = Hom.app h₂.val U x :=
  PresheafOfModules.hom_congr_apply' (congrArg (fun h : _ ⟶ _ => SheafOfModules.Hom.val h) h) U x

/-- **The counit of `f^* ⊣ f_*` undoes the unit on sections of a pushforward.**  This is the right
triangle of the adjunction, read on sections, and it is what makes the counit factor in the
definition of the projection-formula map invisible on sections. -/
theorem counit_app_pullbackUnit (G : SheafOfModules.{u} (structureRingSheaf Z))
    (U : (Opens X.carrier)ᵒᵖ) (a : ToType (((pushforwardFunctor f).obj G).val.obj U)) :
    Hom.app ((pullbackAdjunction f).counit.app G).val ((opensMap f).op.obj U)
        (pullbackUnit f ((pushforwardFunctor f).obj G) U a) = a :=
  hom_app_val_congr ((pullbackAdjunction f).right_triangle_components G) U a

/-- **The projection-formula map on sections.**  It carries the sheafification-unit image of
`a ⊗ y`, for `a` a section of `f_*𝒢` over `U` and `y` a section of `ℋ` over `U`, to the
sheafification-unit image of `a ⊗ η y` over `f⁻¹U`, `η` being the unit of `f^* ⊣ f_*`.

The map is the adjoint transpose of the pullback tensor comparison followed by the counit in the
first factor; the comparison contributes
`Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul` and the counit disappears by
`counit_app_pullbackUnit`. -/
theorem projectionFormulaMap_app_unit_tmul
    (G : SheafOfModules.{u} (structureRingSheaf Z))
    (H : SheafOfModules.{u} (structureRingSheaf X))
    (U : (Opens X.carrier)ᵒᵖ) (a : ToType (((pushforwardFunctor f).obj G).val.obj U))
    (y : ToType (H.val.obj U)) :
    Hom.app (projectionFormulaMap f G H).val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf X)
            (𝟙 (structureRingSheaf X).obj)).unit.app
            (PresheafOfModules.tensorObj (O := X.presheaf) ((pushforwardFunctor f).obj G).val
              H.val)) U (a ⊗ₜ y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf Z)
          (𝟙 (structureRingSheaf Z).obj)).unit.app
          (PresheafOfModules.tensorObj (O := Z.presheaf) G.val ((pullbackFunctor f).obj H).val))
        ((opensMap f).op.obj U)
        (a ⊗ₜ pullbackUnit f H U y) := by
  refine (hom_app_val_congr (projectionFormulaMap_eq_unit_comp f G H) U _).trans ?_
  refine Eq.trans (congrArg (fun t => Hom.app (((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩))).map
      ((pullbackAdjunction f).counit.app G ×ₘ 𝟙 ((pullbackFunctor f).obj H))).val
      ((opensMap f).op.obj U) t)
    (comparison_pullbackUnit_unit_tmul f ((pushforwardFunctor f).obj G) H U a y)) ?_
  refine (tensorSheaf_map_unit_tmul Z ((pullbackAdjunction f).counit.app G)
      (𝟙 ((pullbackFunctor f).obj H)) ((opensMap f).op.obj U)
      (pullbackUnit f ((pushforwardFunctor f).obj G) U a) (pullbackUnit f H U y)).trans ?_
  exact congrArg (fun t => Hom.app ((PresheafOfModules.sheafificationAdjunction
      (R := structureRingSheaf Z) (𝟙 (structureRingSheaf Z).obj)).unit.app
      (PresheafOfModules.tensorObj (O := Z.presheaf) G.val ((pullbackFunctor f).obj H).val))
      ((opensMap f).op.obj U) (t ⊗ₜ pullbackUnit f H U y)) (counit_app_pullbackUnit f G U a)

/-- **The twisted comparison `f_*𝒪_Z ⊗ L ⟶ f_*(f^*L)` on sections**: it carries the
sheafification-unit image of `a ⊗ y` to `a · η y`, the scalar `a` being a section of `𝒪_Z` over
`f⁻¹U`.

The first tensor factor is taken as a free variable `a` named by `ha`, so that the lemma applies
to the closed terms the twist produces without a rewrite having to locate them. -/
theorem projectionFormulaMap_structureUnitor_app_unit_tmul
    (L : SheafOfModules.{u} (structureRingSheaf X)) (U : (Opens X.carrier)ᵒᵖ)
    (α : ToType ((structureRingSheaf Z).obj.obj ((opensMap f).op.obj U)))
    (a : ToType (((pushforwardFunctor f).obj (structureModule Z)).val.obj U))
    (ha : a = Stacks.SheafOfModules.toUnit ((opensMap f).op.obj U) α)
    (y : ToType (L.val.obj U)) :
    Hom.app (projectionFormulaMap f (structureModule Z) L ≫
          (pushforwardFunctor f).map (structureUnitor ((pullbackFunctor f).obj L)).hom).val U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction (R := structureRingSheaf X)
            (𝟙 (structureRingSheaf X).obj)).unit.app
            (PresheafOfModules.tensorObj (O := X.presheaf)
              ((pushforwardFunctor f).obj (structureModule Z)).val L.val)) U
          (a ⊗ₜ y)) =
      α • pullbackUnit f L U y :=
  (congrArg (fun t => Hom.app (structureUnitor ((pullbackFunctor f).obj L)).hom.val
        ((opensMap f).op.obj U) t)
      (projectionFormulaMap_app_unit_tmul f (structureModule Z) L U a y)).trans
    (structureUnitor_tensorSheafUnit_tmul ((pullbackFunctor f).obj L)
      ((opensMap f).op.obj U) α (pullbackUnit f L U y) a ha)

end RingedSpace

end Stacks.AffineProjectionFormula

namespace Stacks.AffineClosedUnion

open Stacks.AffineProjectionFormula

variable {X W Z : Scheme.{u}} (g : W ⟶ Z) (i : Z ⟶ X) (L : X.Modules)

/-- **The restriction leg of the untwisted square, on sections: the comorphism of `g`.**  Over an
open `U` of `X` it is `AlgebraicGeometry.Scheme.Hom.appLE` for `g` by definition, and the
restriction `appLE` composes with is the identity because `(g ≫ i)⁻¹U` and `g⁻¹(i⁻¹U)` are the
same open. -/
theorem pushforwardStructureSheafRestrict_app_eq_sharp (U : (Opens X.carrier)ᵒᵖ)
    (x : ToType ((Stacks.Morphisms.pushforwardStructureSheaf i).val.obj U)) :
    Hom.app (pushforwardStructureSheafRestrict g i (rfl : g ≫ i = g ≫ i)).val U x =
      sharp g.toLRSHom.toShHom ((opensMap i.toLRSHom.toShHom).op.obj U) x := by
  have h := pushforwardStructureSheafRestrict_app_apply g i
    (rfl : g ≫ i = g ≫ i) U.unop x
  rw [Scheme.Hom.appLE] at h
  refine h.trans ?_
  change (CommRingCat.Hom.hom (W.presheaf.map (𝟙 (g ⁻¹ᵁ (i ⁻¹ᵁ U.unop))).op))
      ((CommRingCat.Hom.hom (g.app (i ⁻¹ᵁ U.unop))) x) = _
  simp
  rfl

/-- Mathlib's pullback-composition isomorphism `g^*(i^*L) ≅ (g ≫ i)^*L`, with its type declared at
the `Stacks.RingedSpace.pullbackFunctor` spelling.  The declaration is what makes the module
structure on sections visible to instance search: the scalars of an
`AlgebraicGeometry.Scheme.Modules` are keyed at `AlgebraicGeometry.Scheme.ringCatSheaf`, those of
the lemmas below at `Stacks.RingedSpace.structureRingSheaf`, and the two are definitionally equal
but not interchangeable for instance resolution. -/
def pullbackCompHom :
    (pullbackFunctor g.toLRSHom.toShHom).obj ((pullbackFunctor i.toLRSHom.toShHom).obj L) ⟶
      (pullbackFunctor (g ≫ i).toLRSHom.toShHom).obj L :=
  (Scheme.Modules.pullbackComp g i).hom.app L

/-- **The canonical restriction leg** `i_*(i^*L) ⟶ (g ≫ i)_*((g ≫ i)^*L)`: the pushforward along
`i` of the unit of `g^* ⊣ g_*`, conjugated by the composition isomorphisms of pushforward and of
pullback. -/
def unitRestrict :
    (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L) ⟶
      (Scheme.Modules.pushforward (g ≫ i)).obj ((Scheme.Modules.pullback (g ≫ i)).obj L) :=
  (Scheme.Modules.pushforward i).map
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pullback i).obj L)) ≫
    (Scheme.Modules.pushforwardComp g i).hom.app
      ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback i).obj L)) ≫
    (Scheme.Modules.pushforward (g ≫ i)).map ((Scheme.Modules.pullbackComp g i).hom.app L)

/-- **The unit of `i^* ⊣ i_*` followed by the canonical restriction leg is the unit of
`(g ≫ i)^* ⊣ (g ≫ i)_*`.**  This is the mate identity: `pushforwardComp` is the conjugate of
`pullbackComp.inv` (`AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`), and the
transposed form of that conjugation (`CategoryTheory.unit_conjugateEquiv`) compares the unit of
the composite adjunction with the unit of the adjunction of the composite. -/
theorem unit_comp_unitRestrict :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L ≫ unitRestrict g i L =
      (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ i)).unit.app L := by
  have h := unit_conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction i).comp
    (Scheme.Modules.pullbackPushforwardAdjunction g))
    (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ i))
    (Scheme.Modules.pullbackComp g i).inv L
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have hmate : (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L ≫
      ((Scheme.Modules.pushforward i).map
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
            ((Scheme.Modules.pullback i).obj L)) ≫
        (Scheme.Modules.pushforwardComp g i).hom.app
          ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback i).obj L))) =
      (Scheme.Modules.pullbackPushforwardAdjunction (g ≫ i)).unit.app L ≫
        (Scheme.Modules.pushforward (g ≫ i)).map
          ((Scheme.Modules.pullbackComp g i).inv.app L) := by
    rw [← Category.assoc]
    refine Eq.trans ?_ h
    congr 1
  have h2 := congrArg (fun t => t ≫ (Scheme.Modules.pushforward (g ≫ i)).map
    ((Scheme.Modules.pullbackComp g i).hom.app L)) hmate
  simp only [Category.assoc] at h2
  rw [unitRestrict]
  refine h2.trans ?_
  rw [← Functor.map_comp]
  simp

/-- **The canonical restriction leg, on sections.**  It is the unit of `g^* ⊣ g_*` followed by the
pullback-composition comparison, with nothing in between: the pushforward-composition
isomorphism is the identity on sections. -/
theorem unitRestrict_app_apply (U : (Opens X.carrier)ᵒᵖ)
    (t : ToType ((((Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj L))).val.obj U)) :
    Hom.app (unitRestrict g i L).val U t =
      Hom.app (pullbackCompHom g i L).val
        ((opensMap g.toLRSHom.toShHom).op.obj ((opensMap i.toLRSHom.toShHom).op.obj U))
        (pullbackUnit g.toLRSHom.toShHom
          ((pullbackFunctor i.toLRSHom.toShHom).obj L)
          ((opensMap i.toLRSHom.toShHom).op.obj U) t) := rfl

/-- **The canonical restriction leg carries the restriction of a section of `L` to its
restriction.**  This is `unit_comp_unitRestrict` read on sections. -/
theorem unitRestrict_app_pullbackUnit (U : (Opens X.carrier)ᵒᵖ)
    (y : ToType (L.val.obj U)) :
    Hom.app (unitRestrict g i L).val U (pullbackUnit i.toLRSHom.toShHom L U y) =
      pullbackUnit (g ≫ i).toLRSHom.toShHom L U y :=
  hom_app_val_congr (unit_comp_unitRestrict g i L) U y

/-- **The canonical restriction leg on the sections the twist produces**: a scalar multiple of the
restriction of a section of `L` goes to the image scalar times the restriction.  The unit of
`g^* ⊣ g_*` is semilinear over the comorphism of `g` and the pullback-composition comparison is
linear, so the scalar comes out.

The image scalar is taken as a free variable `β` named by `hβ`, so that the lemma applies at the
closed term the twist produces without a rewrite having to locate it. -/
theorem unitRestrict_app_smul_pullbackUnit (U : (Opens X.carrier)ᵒᵖ)
    (α : ToType ((structureRingSheaf Z.toRingedSpace).obj.obj
      ((opensMap i.toLRSHom.toShHom).op.obj U)))
    (β : ToType ((structureRingSheaf W.toRingedSpace).obj.obj
      ((opensMap (g ≫ i).toLRSHom.toShHom).op.obj U)))
    (hβ : β = sharp g.toLRSHom.toShHom ((opensMap i.toLRSHom.toShHom).op.obj U) α)
    (y : ToType (L.val.obj U)) :
    Hom.app (unitRestrict g i L).val U (α • pullbackUnit i.toLRSHom.toShHom L U y) =
      β • pullbackUnit (g ≫ i).toLRSHom.toShHom L U y := by
  subst hβ
  have hfin : Hom.app (pullbackCompHom g i L).val
        ((opensMap g.toLRSHom.toShHom).op.obj ((opensMap i.toLRSHom.toShHom).op.obj U))
        (pullbackUnit g.toLRSHom.toShHom ((pullbackFunctor i.toLRSHom.toShHom).obj L)
          ((opensMap i.toLRSHom.toShHom).op.obj U)
          (pullbackUnit i.toLRSHom.toShHom L U y)) =
      pullbackUnit (g ≫ i).toLRSHom.toShHom L U y :=
    unitRestrict_app_pullbackUnit g i L U y
  change Hom.app (pullbackCompHom g i L).val
      ((opensMap g.toLRSHom.toShHom).op.obj ((opensMap i.toLRSHom.toShHom).op.obj U))
      (pullbackUnit g.toLRSHom.toShHom ((pullbackFunctor i.toLRSHom.toShHom).obj L)
        ((opensMap i.toLRSHom.toShHom).op.obj U)
        (α • pullbackUnit i.toLRSHom.toShHom L U y)) = _
  rw [pullbackUnit_smul]
  refine (map_smul _ _ _).trans ?_
  rw [hfin]
  rfl

/-- **`twistedRestrict` is the canonical restriction leg** — the obligation
`StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.TwistedSections` recorded as owed.

`CategoryTheory.Iso.inv_comp_eq` removes the inverted projection formula from the left of
`twistedRestrict`, after which both sides are morphisms out of the sheaf tensor product
`i_*𝒪_Z ⊗ L` and the claim can be checked on the sheafification-unit image of a pure tensor
`x ⊗ y`.  There both sides are `g^♯x · η y`: on the left by
`Stacks.AffineProjectionFormula.projectionFormulaMap_structureUnitor_app_unit_tmul` at `g ≫ i`
together with `pushforwardStructureSheafRestrict_app_eq_sharp`, on the right by the same lemma at
`i` together with `unitRestrict_app_smul_pullbackUnit`. -/
theorem twistedRestrict_eq_unitRestrict [IsClosedImmersion i] [IsClosedImmersion (g ≫ i)] :
    twistedRestrict g i (rfl : g ≫ i = g ≫ i) L = unitRestrict g i L := by
  rw [twistedRestrict, Iso.inv_comp_eq]
  refine Eq.trans (congrArg (fun tensorMap => tensorMap ≫ (twistPushforwardIso (g ≫ i) L).hom)
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map.{u, u, u, u, u} X.sheaf
      (pushforwardStructureSheafRestrict g i (rfl : g ≫ i = g ≫ i)) (𝟙 L)).symm) ?_
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.tensorObj_hom_ext fun U x y => ?_)
  have key : ∀ (x : ToType ((structureRingSheaf Z.toRingedSpace).obj.obj
        ((opensMap i.toLRSHom.toShHom).op.obj U)))
      (y : ToType (L.val.obj U)),
      Hom.app (((Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf))).map
            (pushforwardStructureSheafRestrict g i (rfl : g ≫ i = g ≫ i) ×ₘ 𝟙 L) ≫
          (twistPushforwardIso (g ≫ i) L).hom).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := structureRingSheaf X.toRingedSpace)
              (𝟙 (structureRingSheaf X.toRingedSpace).obj)).unit.app
              (PresheafOfModules.tensorObj (O := X.toRingedSpace.presheaf)
                (Stacks.Morphisms.pushforwardStructureSheaf i).val L.val)) U (x ⊗ₜ y)) =
        Hom.app ((twistPushforwardIso i L).hom ≫ unitRestrict g i L).val U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := structureRingSheaf X.toRingedSpace)
              (𝟙 (structureRingSheaf X.toRingedSpace).obj)).unit.app
              (PresheafOfModules.tensorObj (O := X.toRingedSpace.presheaf)
                (Stacks.Morphisms.pushforwardStructureSheaf i).val L.val)) U (x ⊗ₜ y)) := by
    intro x y
    have e1 := tensorSheaf_map_unit_tmul X.toRingedSpace
      (pushforwardStructureSheafRestrict g i (rfl : g ≫ i = g ≫ i)) (𝟙 L) U x y
    have e2 := projectionFormulaMap_structureUnitor_app_unit_tmul
      (g ≫ i).toLRSHom.toShHom L U
      (Hom.app (pushforwardStructureSheafRestrict g i (rfl : g ≫ i = g ≫ i)).val U x)
      (Hom.app (pushforwardStructureSheafRestrict g i (rfl : g ≫ i = g ≫ i)).val U x) rfl y
    have e3 := projectionFormulaMap_structureUnitor_app_unit_tmul
      i.toLRSHom.toShHom L U x x rfl y
    have e4 := congrArg (fun t => Hom.app (unitRestrict g i L).val U t) e3
    refine ((congrArg (fun t => Hom.app (twistPushforwardIso (g ≫ i) L).hom.val U t) e1).trans
      e2).trans (Eq.trans ?_ e4.symm)
    exact (unitRestrict_app_smul_pullbackUnit g i L U x
      (Hom.app (pushforwardStructureSheafRestrict g i (rfl : g ≫ i = g ≫ i)).val U x)
      (pushforwardStructureSheafRestrict_app_eq_sharp g i U x) y).symm
  exact key x y

/-- `twistedRestrict`, for an arbitrary factorisation `k = g ≫ i`, takes the unit of `i^* ⊣ i_*`
to the unit of `k^* ⊣ k_*`. -/
theorem unit_comp_twistedRestrict {k : W ⟶ X} (hk : g ≫ i = k)
    [IsClosedImmersion i] [IsClosedImmersion k] :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L ≫ twistedRestrict g i hk L =
      (Scheme.Modules.pullbackPushforwardAdjunction k).unit.app L := by
  subst hk
  rw [twistedRestrict_eq_unitRestrict]
  exact unit_comp_unitRestrict g i L

/-- **The restriction legs of the twisted square are restriction of sections**: over an open `V`,
`twistedRestrict` carries the restriction of a section of `L` to its restriction. -/
theorem twistedRestrict_app_unit_app {k : W ⟶ X} (hk : g ≫ i = k)
    [IsClosedImmersion i] [IsClosedImmersion k] (V : X.Opens) (c : Γ(L, V)) :
    (twistedRestrict g i hk L).app V
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L).app V c) =
      ((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app L).app V c :=
  hom_app_val_congr (unit_comp_twistedRestrict g i L hk) (op V) c

/-- `twistedRestrict` and the canonical restriction leg vanish on the same sections.  The two have
different codomains when `k` is not literally `g ≫ i`, so this is the form in which the
identification transfers a vanishing hypothesis. -/
theorem twistedRestrict_app_eq_zero_iff {k : W ⟶ X} (hk : g ≫ i = k)
    [IsClosedImmersion i] [IsClosedImmersion k] (V : X.Opens)
    (t : Γ((Scheme.Modules.pullback i).obj L, i ⁻¹ᵁ V)) :
    (twistedRestrict g i hk L).app V t = 0 ↔ (unitRestrict g i L).app V t = 0 := by
  subst hk
  rw [twistedRestrict_eq_unitRestrict]

variable (I₁ I₂ : X.IdealSheafData)

/-- **The vanishing form of the twisted square with every leg a canonical map.**  A section of
`i₂^*L` over the preimage of `V` whose canonical restriction to the scheme-theoretic intersection
vanishes is the restriction of a unique section of `L` over `V` vanishing on the first closed
subscheme.  This is
`Stacks.AffineClosedUnion.existsUnique_unit_app_eq_zero_of_inf_eq_bot` with its one remaining
`twistedRestrict` hypothesis read through `twistedRestrict_eq_unitRestrict`. -/
theorem existsUnique_unit_app_eq_zero_of_unitRestrict_eq_zero (h : I₁ ⊓ I₂ = ⊥)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (V : X.Opens)
    (b : Γ((Scheme.Modules.pullback I₂.subschemeι).obj L, I₂.subschemeι ⁻¹ᵁ V))
    (hb : (unitRestrict (AlgebraicGeometry.Scheme.IdealSheafData.inclusion
      (le_sup_right : I₂ ≤ I₁ ⊔ I₂)) I₂.subschemeι L).app V b = 0) :
    ∃! c : Γ(L, V),
      ((Scheme.Modules.pullbackPushforwardAdjunction I₁.subschemeι).unit.app L).app V c = 0 ∧
        ((Scheme.Modules.pullbackPushforwardAdjunction I₂.subschemeι).unit.app L).app V c = b :=
  existsUnique_unit_app_eq_zero_of_inf_eq_bot L I₁ I₂ h V b
    ((twistedRestrict_app_eq_zero_iff _ I₂.subschemeι L
      (AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι _) V b).2 hb)

end Stacks.AffineClosedUnion

end
