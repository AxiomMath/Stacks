module

public import Mathlib.CategoryTheory.Adjunction.Opposites
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Colimits computed along a right adjoint on a diagram inverting the unit

Let `adj : L ⊣ R` be an adjunction between `L : C ⥤ D` and `R : D ⥤ C`, with unit
`η : 𝟭 C ⟹ L ⋙ R`, and let `F : Cᵒᵖ ⥤ A` be a diagram on the opposite of the larger category.
This file shows that the colimit of `F` over `Cᵒᵖ` may be computed over the smaller index
category `Dᵒᵖ` along `R.op`, *provided* `F` inverts the unit: if `F.map (η.app X).op` is an
isomorphism for every `X : C`, then whiskering a colimit cocone on `F` by `R.op` again gives a
colimit cocone, now on `R.op ⋙ F`.

Unit-inversion is essential and is the only hypothesis beyond the adjunction.  Finality of `L.op`
— which holds unconditionally, since `adj.op : R.op ⊣ L.op` exhibits `L.op` as a right adjoint —
only reduces a cocone on `R.op ⋙ F` to its further whiskering by `L.op`, a cocone on
`L.op ⋙ R.op ⋙ F`.  Identifying *that* diagram with `F` is exactly what inverting the unit
provides, and without it the reduction stops there: the two colimits genuinely differ.

The motivating instance is Čech cohomology computed from one-member coverings (Stacks 03P0).
There `R` is the inclusion of the one-member coverings of an object into all of its coverings,
`L` sends a covering to the one-member covering by the disjoint union of its members, and the
unit is the refinement map.  A presheaf inverts that refinement precisely when it is a sheaf
for the covering, which is why the reduction to one-member coverings is available for sheaves
and for nothing else.

## Main results

* `CategoryTheory.Limits.natIsoOfInvertsUnit` — a diagram inverting the unit is naturally
  isomorphic to its restriction along `R.op` and re-extension along `L.op`.
* `CategoryTheory.Limits.isColimitWhiskerOfInvertsUnit` — the whiskering by `R.op` of a colimit
  cocone on such a diagram is a colimit cocone.
* `CategoryTheory.Limits.hasColimit_whisker_of_invertsUnit` — existence of the colimit transfers
  to `R.op ⋙ F`.
* `CategoryTheory.Limits.colimitIsoOfInvertsUnit` and
  `CategoryTheory.Limits.ι_colimitIsoOfInvertsUnit` — the resulting isomorphism of colimits,
  and its compatibility with the cocone legs, which is what pins it down.

## Implementation notes

The identification of `(c.whisker R.op).whisker L.op` with the cocone obtained from `c` by
precomposing with `natIsoOfInvertsUnit` is leg-by-leg the cocone law `c.w` applied to
`(η.app X).op`; the two cocones share their point, so `CategoryTheory.Limits.Cocone.ext` with
`Iso.refl` suffices.

The three universes of `C`, `D` and `A` are independent, as are their three morphism universes:
nothing here compares objects of different categories.

## References

* [Stacks Project, Tag 03P0](https://stacks.math.columbia.edu/tag/03P0)
* [Stacks Project, Tag 04E6](https://stacks.math.columbia.edu/tag/04E6)
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A] {L : C ⥤ D} {R : D ⥤ C}

/-- **A diagram inverting the unit is recovered from its restriction along `R.op`.**  If
`F : Cᵒᵖ ⥤ A` sends every opposed unit component `(adj.unit.app X).op` to an isomorphism, then
the composite `L.op ⋙ R.op ⋙ F` is naturally isomorphic to `F`, the component at `Z : Cᵒᵖ`
being `F.map (adj.unit.app Z.unop).op`.

Naturality is naturality of the unit, transported through `F` after taking opposites. -/
noncomputable def natIsoOfInvertsUnit (adj : L ⊣ R) (F : Cᵒᵖ ⥤ A)
    (hF : ∀ X : C, IsIso (F.map (adj.unit.app X).op)) : L.op ⋙ R.op ⋙ F ≅ F :=
  NatIso.ofComponents (fun Z => haveI := hF Z.unop; asIso (F.map (adj.unit.app Z.unop).op))
    (fun f => by
      dsimp
      rw [← F.map_comp, ← F.map_comp]
      refine congrArg F.map (Quiver.Hom.unop_inj ?_)
      simp)

/-- **A colimit over `Cᵒᵖ` is computed over `Dᵒᵖ` as soon as the diagram inverts the unit.**
Given an adjunction `adj : L ⊣ R` and a diagram `F : Cᵒᵖ ⥤ A` inverting the opposed unit, any
colimit cocone `c` on `F` whiskers along `R.op` to a colimit cocone on `R.op ⋙ F`.

The proof has two halves.  The functor `L.op` is final, being the right adjoint of `R.op` by
`CategoryTheory.Adjunction.op`, so `CategoryTheory.Functor.Final.isColimitWhiskerEquiv` reduces
the claim to `(c.whisker R.op).whisker L.op` being a colimit cocone on `L.op ⋙ R.op ⋙ F`.  That
cocone is `c` precomposed with `natIsoOfInvertsUnit`, which is a colimit cocone because `c` is:
here is where inverting the unit is used. -/
noncomputable def isColimitWhiskerOfInvertsUnit (adj : L ⊣ R) {F : Cᵒᵖ ⥤ A} (c : Cocone F)
    (hc : IsColimit c) (hF : ∀ X : C, IsIso (F.map (adj.unit.app X).op)) :
    IsColimit (c.whisker R.op) :=
  haveI : L.op.Final := Functor.final_of_adjunction adj.op
  Functor.Final.isColimitWhiskerEquiv L.op (c.whisker R.op)
    (((IsColimit.precomposeHomEquiv (natIsoOfInvertsUnit adj F hF) c).symm hc).ofIsoColimit
      (Cocone.ext (Iso.refl _) (fun j => by
        dsimp [natIsoOfInvertsUnit]
        rw [Category.comp_id]
        exact c.w (adj.unit.app j.unop).op)))

/-- **Existence of the colimit transfers along `R.op`.**  If `F : Cᵒᵖ ⥤ A` inverts the opposed
unit of `adj : L ⊣ R` and has a colimit, then so does its restriction `R.op ⋙ F`, the colimit
cocone being the whiskering of a colimit cocone on `F`. -/
theorem hasColimit_whisker_of_invertsUnit (adj : L ⊣ R) {F : Cᵒᵖ ⥤ A} [HasColimit F]
    (hF : ∀ X : C, IsIso (F.map (adj.unit.app X).op)) : HasColimit (R.op ⋙ F) :=
  HasColimit.mk
    { cocone := (colimit.cocone F).whisker R.op
      isColimit := isColimitWhiskerOfInvertsUnit adj _ (colimit.isColimit F) hF }

/-- **The comparison isomorphism of colimits.**  For `F : Cᵒᵖ ⥤ A` inverting the opposed unit of
`adj : L ⊣ R`, the colimit of the restriction `R.op ⋙ F` over `Dᵒᵖ` agrees with the colimit of
`F` over `Cᵒᵖ`.

See `ι_colimitIsoOfInvertsUnit` for the compatibility with the cocone legs, which is what makes
this the comparison map and not merely some isomorphism. -/
noncomputable def colimitIsoOfInvertsUnit (adj : L ⊣ R) {F : Cᵒᵖ ⥤ A} [HasColimit F]
    [HasColimit (R.op ⋙ F)] (hF : ∀ X : C, IsIso (F.map (adj.unit.app X).op)) :
    colimit (R.op ⋙ F) ≅ colimit F :=
  (colimit.isColimit (R.op ⋙ F)).coconePointUniqueUpToIso
    (isColimitWhiskerOfInvertsUnit adj (colimit.cocone F) (colimit.isColimit F) hF)

/-- **The comparison isomorphism respects the cocone legs.**  The leg of `colimit (R.op ⋙ F)` at
`X : Dᵒᵖ`, followed by `colimitIsoOfInvertsUnit`, is the leg of `colimit F` at `R.op.obj X`.
Since the legs jointly determine a morphism out of a colimit, this characterises
`colimitIsoOfInvertsUnit` completely. -/
theorem ι_colimitIsoOfInvertsUnit (adj : L ⊣ R) {F : Cᵒᵖ ⥤ A} [HasColimit F]
    [HasColimit (R.op ⋙ F)] (hF : ∀ X : C, IsIso (F.map (adj.unit.app X).op)) (X : Dᵒᵖ) :
    colimit.ι (R.op ⋙ F) X ≫ (colimitIsoOfInvertsUnit adj hF).hom = colimit.ι F (R.op.obj X) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ X

end CategoryTheory.Limits

end
