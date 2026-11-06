module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedProper

/-!
# Separatedness in the universe of the site, read through the trivial universe lift

`AlgebraicGeometry.Space.IsSeparatedULift.{w}` is separatedness (Stacks 03HL) for a morphism of
presheaves with values in `Type (max w u)`, its scheme-valued points being the morphisms out of
`CategoryTheory.uliftYoneda.{w}.obj U`. For `w = 0` the presheaves take values in `Type u`, the
universe of the site, where separatedness is `AlgebraicGeometry.Space.IsSeparated`, with the
scheme-valued points the morphisms out of `CategoryTheory.yoneda.obj U`. The two notions agree,
as does every property of morphisms read relative to the two embeddings.

## Main results

* `AlgebraicGeometry.Space.relative_uliftYoneda_zero_iff`: a property of morphisms relative to
  `CategoryTheory.uliftYoneda.{0}` is the same property relative to `CategoryTheory.yoneda`.
* `AlgebraicGeometry.Space.isSeparatedULift_zero_iff_isSeparated`.

## Implementation notes

The universe lift `uliftFunctor.{0}` of `Type u` is isomorphic to the identity, so a morphism of
`Type u`-valued presheaves is isomorphic, as an arrow, to its lift, and relative properties
respect isomorphisms of arrows. The lift is then compared with the morphism itself by
`AlgebraicGeometry.Space.relative_comp_map_iff`, as in
`AlgebraicGeometry.Space.isSeparatedULift_whiskerRight_iff`.

## References

* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Relative properties through the trivial universe lift.** For presheaves of `Type u` on a
category with morphisms in `Type u`, a morphism has a property `P` relative to
`CategoryTheory.uliftYoneda.{0}` exactly when it has `P` relative to `CategoryTheory.yoneda`:
the universe lift `uliftFunctor.{0}` of `Type u` is isomorphic to the identity, so the morphism
is isomorphic, as an arrow, to its lift, and its lift has `P` relative to `uliftYoneda.{0}`
exactly when it has `P` relative to `yoneda`
(`AlgebraicGeometry.Space.relative_comp_map_iff`). -/
theorem relative_uliftYoneda_zero_iff {C : Type*} [Category.{u} C] (P : MorphismProperty C)
    {F G : Cᵒᵖ ⥤ Type u} (f : F ⟶ G) :
    P.relative uliftYoneda.{0} f ↔ P.relative yoneda f := by
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type u)).obj uliftFunctor.{0, u}
  let ε : 𝟭 (Type u) ≅ uliftFunctor.{0, u} :=
    NatIso.ofComponents (fun X => Equiv.ulift.symm.toIso)
  let e : Arrow.mk f ≅ Arrow.mk (H.map f) :=
    Arrow.isoMk ((Functor.rightUnitor F).symm ≪≫ Functor.isoWhiskerLeft F ε)
      ((Functor.rightUnitor G).symm ≪≫ Functor.isoWhiskerLeft G ε) (by ext; rfl)
  exact ((P.relative uliftYoneda.{0}).arrow_mk_iso_iff e).trans
    (relative_comp_map_iff yoneda H P f)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_LargeValuedSeparatedSmall
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **Separatedness through the trivial universe lift.** A morphism of presheaves of `Type u` on
the big fppf site of `S` is separated in the sense of
`AlgebraicGeometry.Space.IsSeparatedULift.{0}`, with scheme-valued points read through
`CategoryTheory.uliftYoneda.{0}`, exactly when it is separated in the sense of
`AlgebraicGeometry.Space.IsSeparated`. -/
theorem isSeparatedULift_zero_iff_isSeparated {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : F ⟶ G) : IsSeparatedULift.{0} B S hS q ↔ IsSeparated B S hS q :=
  relative_uliftYoneda_zero_iff _ (pullback.diagonal q)

end AlgebraicGeometry.Space

end
